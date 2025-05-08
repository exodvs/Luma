package main

import (
	"bufio"
	"flag"
	"fmt"
	"image"
	"slices"

	_ "image/gif"

	_ "image/jpeg"
	"io"
	"log"
	"math"
	"math/rand"
	"os"
	"regexp"
	"runtime/pprof"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	fastpng "github.com/amarburg/go-fast-png"
	"gocv.io/x/gocv"

	_ "golang.org/x/image/bmp"

	_ "golang.org/x/image/tiff"
)

import "C"

var start = time.Now().UnixNano()

//var arraySize = 0

//var wg sync.WaitGroup

var cpuprofile = flag.String("cpuprofile", "", "write cpu profile to file")

/*
Grids defined below have a variable dimCornAvg, which stores the
dimensions, corners, and average brightness. It was originally added
to aid in sorting, but other uses have been found. The following
global variables suffixed with _64 are ANDed with the dimCornAvg
value in order to focus on certain aspects without having to
make array calls or to check several different aspects at onece.
*/
var W_64 uint64 = 0xFF00000000000000
var H_64 uint64 = 0x00FF000000000000
var DIM_64 uint64 = W_64 | H_64
var C1_64 uint64 = 0x000000FF00000000
var C2_64 uint64 = 0x00000000FF000000
var C3_64 uint64 = 0x0000000000FF0000
var C4_64 uint64 = 0x000000000000FF00
var AVG_64 uint64 = 0x0000FF0000000000
var RAN_64 uint64 = 0x00000000000000FF

/*Absolute difference between two unsigned 8-bit numbers.*/
func byteAbsDiff(a uint8, b uint8) uint8 {
	if a == b {
		return 0
	}
	if a > b {
		return a - b
	}
	return b - a
}

/*
Absolute value of an integer, currently used in a single-
line function that involves string comparison.
*/
func absInt(x int) int {
	if x < 0 {
		return 0 - x
	}
	return x
}

/*
A struct for a grid, containing a width, height, and an array of
gray pixels. It also keeps track of the highest, lowest, and
average value of these. It also once kept track of the median,
but the sorting involved was time-consuming and of limited
utility.
*/
type Grid struct {
	w__     uint8
	h__     uint8
	avgLuma uint8
	medLuma uint8
	maxLuma uint8
	minLuma uint8
	//array      [][]uint8
	sum        uint8
	coord      uint64
	dimCornAvg uint64 /*DIMensions, CORNers, AVeraGE, used for sorting and other purposes*/
	corners    uint32
	offset     int
	maxLoc     int
	minLoc     int
}

func (g Grid) getW() uint8 {
	return g.w__
}

func (g Grid) getH() uint8 {
	return g.h__
}

/*
This is a struct for a tree containing bounding x and y values, minimum
split values, children, and a two-bit variable to determine if it has
children. This is used to determine fragments of images to be turned into
grids.
*/
type Tree struct {
	x1          uint64
	x2          uint64
	y1          uint64
	y2          uint64
	hasChildren uint8
	lTree       *Tree
	rTree       *Tree
	leafNum     int
}

/*This is a recursive instantiation method for a tree.*/
func generateTree(x1In uint64, x2In uint64, y1In uint64, y2In uint64, minIn uint64, maxIn uint64, rBits uint64, rBytes uint64) *Tree {
	t := Tree{
		x1:          x1In,
		x2:          x2In,
		y1:          y1In,
		y2:          y2In,
		hasChildren: 0,
		leafNum:     0,
	}
	/*This determines which axis is divided if both are above the maximum allowable dimensions*/
	for rBits == 0 {
		rBits = rand.Uint64()
	}
	/*This determines the size of a division*/
	for (rBytes & 0xFFFF) < 2*minIn {
		rBytes = rand.Uint64()
	}
	/*If the horizontal endpoints are greater than the maximum allowed and the vertical is not OR the lowest
	bit in rBits is 0, subdivide horizontally*/
	if t.x2-t.x1 > maxIn && (t.y2-t.y1 <= maxIn || rBits%2 == 0) {
		rBits >>= 1
		mid := (t.x1 + minIn) + ((rBytes & 0xFFFF) % (t.x2 - t.x1 - (2 * minIn)))
		rBytes >>= 16
		t.hasChildren = 3
		t.lTree = generateTree(t.x1, mid, t.y1, t.y2, minIn, maxIn, rBits, rBytes)
		t.rTree = generateTree(mid, t.x2, t.y1, t.y2, minIn, maxIn, rBits, rBytes)
		t.leafNum = t.lTree.leafNum + t.rTree.leafNum
		/*If the vertical endpoints are greater than the maximum allowed and the horizontal is not OR the lowest
		bit in rBits is 1, subdivide verically*/
	} else if t.y2-t.y1 > maxIn {
		mid := (t.y1 + minIn) + ((rBytes & 0xFFFF) % (t.y2 - t.y1 - (2 * minIn)))
		t.hasChildren = 3
		rBytes >>= 16
		t.lTree = generateTree(t.x1, t.x2, t.y1, mid, minIn, maxIn, rBits, rBytes)
		t.rTree = generateTree(t.x1, t.x2, mid, t.y2, minIn, maxIn, rBits, rBytes)
		t.leafNum = t.lTree.leafNum + t.rTree.leafNum
		/*If both are within the proper range, set this tree to a leaf*/
	} else {
		t.leafNum = 1
	}
	return &t
}

/*
Checks if the absolute difference between two grids exceeds a certain maximum value.
There used to be a "g2," which now is a ghost variable mentioned in the comments to
make things clearer. The last several parameters refer to what it was, and are acquired
outside the loop to increase speed.
*/
func gridDiffNaphil(g1 Grid, maxSum uint32, naphilArray1 []uint8, naphilArray2 []uint8, area int, min2 uint8, max2 uint8, start_2 int, end_2 int) uint32 {
	sum := uint32(0)
	area_32 := uint32(area)
	var p1, p2, diff uint8
	maxDiff_8 := uint8(maxSum / area_32)
	min1 := g1.minLuma
	max1 := g1.maxLuma
	start_1 := g1.offset
	end_1 := start_1 + area
	i1 := end_1
	i2 := end_2
	/*Edge case, the first grid's pixels all equal each other*/
	if min1 == max1 {
		if min2 == max2 {
			/*Both grids have the same unique value as each other*/
			if min1 == min2 {
				return 0
			}
			/*g1 is above g2*/
			if min1 > min2 {
				return area_32 * uint32(min1-min2)
			}
			/*g2 is above g1*/
			return area_32 * uint32(min2-min1)
		}
		/*The following two scenarios are set apart because they
		have no risk of bit underflow.*/
		/*All values in g2 are above g1*/
		if min2 >= max1 {
			g1_32 := (uint32(max1) * area_32)
			maxSum_alt := maxSum + g1_32
			for i2 > start_2 {
				i2--
				sum += uint32(naphilArray2[i2])
				if sum > maxSum_alt {
					return sum
				}
			}
			return sum - g1_32
		}
		/*All values in g1 are above g2*/
		if min1 >= max2 {
			for i2 > start_2 {
				i2--
				sum += uint32(min1 - naphilArray2[i2])
				if sum > maxSum {
					return sum
				}
			}
			return sum
		}
		/*The values in g2 are interspersed above
		and below g1*/
		for i2 > start_2 {
			i2--
			p2 = naphilArray2[i2]
			if p2 != max1 {
				diff = p2 - max1
				if max1 > p2 {
					diff = max1 - p2
				}
				sum += uint32(diff)
				if sum > maxSum {
					return sum
				}
			}
		}
		return sum
	}
	/*All values in g2 are the same*/
	if min2 == max2 {
		/*All values in g1 are above g2*/
		if min1 >= max2 {
			g2_32 := (uint32(max2) * area_32)
			maxSum_alt := maxSum + g2_32
			for i1 > start_1 {
				i1--
				sum += uint32(naphilArray1[i1])
				if sum > maxSum_alt {
					return sum
				}
			}
			return sum - g2_32
		}
		/*All values in g1 are below g2*/
		if min2 >= max1 {
			for i1 > start_1 {
				i1--
				sum += uint32(min2 - naphilArray1[i1])
				if sum > maxSum {
					return sum
				}
			}
			return sum
		}
		/*The values in g1 are interspersed above and below g2*/
		for i1 != start_1 {
			i1--
			p1 = naphilArray1[i1]
			if p1 > max2 {
				diff = p1 - max2
				if max2 > p1 {
					diff = max2 - p1
				}
				sum += uint32(diff)
				if sum > maxSum {
					return sum
				}
			}
		}
		return sum
	}
	/*Edge case, all of the pixel values in g1 are greater than even
	the highest value in g2*/
	if min1 >= max2 {
		/*This value is greater than the allowable difference*/
		if min1-max2 >= maxDiff_8 {
			return math.MaxUint32
		}
		for i1 > start_1 {
			i1--
			i2--
			p1 = naphilArray1[i1]
			p2 = naphilArray2[i2]
			if p1 != p2 {
				diff = p1 - p2
				sum += uint32(diff)
				if sum > maxSum {
					return sum
				}
			}
		}
		return sum
	}
	if min2 >= max1 {
		if min2-max1 >= maxDiff_8 {
			return math.MaxUint32
		}
		for i1 > start_1 {
			i1--
			i2--
			p1 = naphilArray1[i1]
			p2 = naphilArray2[i2]
			if p1 != p2 {
				diff = p2 - p1
				sum += uint32(diff)
				if sum > maxSum {
					return sum
				}
			}
		}
		return sum
	}
	/*The loop is unrolled*/
	start_l := start_1 + (area % 4)
	for i1 > start_l {
		i1--
		i2--
		p1 = naphilArray1[i1]
		p2 = naphilArray2[i2]
		if p1 != p2 {
			diff = p1 - p2
			if p1 < p2 {
				diff = p2 - p1
			}
			sum += uint32(diff)
			if sum > maxSum {
				return sum
			}
		}
		i1--
		i2--
		p1 = naphilArray1[i1]
		p2 = naphilArray2[i2]
		if p1 != p2 {
			diff = p1 - p2
			if p1 < p2 {
				diff = p2 - p1
			}
			sum += uint32(diff)
			if sum > maxSum {
				return sum
			}
		}
		i1--
		i2--
		p1 = naphilArray1[i1]
		p2 = naphilArray2[i2]
		if p1 != p2 {
			diff = p1 - p2
			if p1 < p2 {
				diff = p2 - p1
			}
			sum += uint32(diff)
			if sum > maxSum {
				return sum
			}
		}
		i1--
		i2--
		p1 = naphilArray1[i1]
		p2 = naphilArray2[i2]
		if p1 != p2 {
			diff = p1 - p2
			if p1 < p2 {
				diff = p2 - p1
			}
			sum += uint32(diff)
			if sum > maxSum {
				return sum
			}
		}
	}
	if i1 <= start_1 {
		return sum
	}
	/*This handles loops which are not unrolled*/
	for i1 > start_1 {
		i1--
		i2--
		p1 = naphilArray1[i1]
		p2 = naphilArray2[i2]
		if p1 != p2 {
			diff = p1 - p2
			if p1 < p2 {
				diff = p2 - p1
			}
			sum += uint32(diff)
			if sum > maxSum {
				return sum
			}
		}
	}
	return sum
}

/*This is Brian Kernighan's bit-counting algorithm.*/
func kern(x uint8) int {
	count := 0
	for x != 0 {
		count += 1
		x &= (x - 1)
	}
	return count
}

/*
Corner mismatch between two grids.
*/
func gridMismatchCorn(d1 uint64, d2 uint64, margInt uint64) uint8 {
	var d1_mod, d2_mod uint64
	c := uint8(4)

	/*From the outset, the corners occupy the bottom 32 bits of a
	64-bit number for technical reasons explained above. The loop
	examines the bottom 8, and shifts the corners each time until
	it finds either two corresponding corners between grids that
	are very different or one of the sets of corners is zeroed
	out.
	*/
loopStart:
	d1_mod = d1 & 0xFF
	d2_mod = d2 & 0xFF
	if d1_mod != d2_mod {
		d1_mod >>= 24
		d2_mod >>= 24
		if (d1_mod > d2_mod && d1_mod-d2_mod > margInt) ||
			(d2_mod > d1_mod && d2_mod-d1_mod > margInt) {
			return c
		}
	}
	c--
	d1 >>= 8
	d2 >>= 8
	if d1 != 0 && d2 != 0 {
		goto loopStart
	}
	if d1 == 0 {
		goto loopStart2
	}
	if d2 == 0 {
		goto loopStart1
	}
	goto loopEnd
	/*In these two loops, one of the grids has zero as its
	remaining corners, and the other one is simply checked
	if any of its corners' absolute values exceeds the margin.*/
loopStart1:
	if d1 != 0 {
		d1_mod = d1 & 0xFF
		if d1_mod > margInt {
			return c
		}
		c--
		d1 >>= 8
		goto loopStart1
	}
loopStart2:
	if d2 != 0 {
		d2_mod = d2 & 0xFF
		if d2_mod > margInt {
			return c
		}
		c--
		d2 >>= 8
		goto loopStart2
	}
loopEnd:
	return 0
}

/*
This peforms a binary search on a grid array to check for the
average or a corner. A goto loop was chosen over recursion due
to overhead concerns.
*/
func binarySearchGridArray(array []Grid, a int, b int, shift_amount uint64, query uint64) int {
	var m int
searchStart:
	if a < len(array) && b < len(array) && a < b {
		m = a + ((b - a) / 2)
		if (array[m].dimCornAvg>>shift_amount)&255 < query {
			a = m + 1
			goto searchStart
		}
		b = m
		goto searchStart
	}
	return a
}

/*
This finds not only the last grid in an array with the same
average or corner value as the current cursor, but also the
last with one of a similar (defined by the margin) value.
*/
func findEndpoints(array []Grid, cursor int, shift_amount uint64, end_in int, m_64 uint64) (uint64, int, int) {
	var marg_end, end_out int
	var query uint64
	query = array[cursor].dimCornAvg
	if shift_amount != 0 {
		query >>= shift_amount
	}
	query &= 0xFF
	end_out = end_in
	if query < 255 {
		end_out = binarySearchGridArray(array, cursor+1, end_in, shift_amount, query+1)
	}
	marg_end = end_in
	if query < 255-m_64 {
		marg_end = binarySearchGridArray(array, end_out+1, end_in, shift_amount, query+m_64)
	}
	return query, end_out, marg_end
}

/*
This finds the first and last grids with average and corner
values immediately above the one at cursor i.
*/
func findNewEndpoints(array []Grid, i int, j int, shift_amount uint64, end int) (int, int, bool) {
	tempValue := array[i].dimCornAvg
	if shift_amount != 0 {
		tempValue >>= shift_amount
	}
	tempValue &= 0xFF
	if tempValue == 255 {
		return j, j + 1, true
	}
	new_start := binarySearchGridArray(array, j, end, 24, tempValue+1)
	new_end := end
	if tempValue < 254 {
		new_end = binarySearchGridArray(array, new_start+1, end, 24, tempValue+2)
	}
	return new_start, new_end, false
}

/*
This blends the above functions to find the first and last grids
for a specific query, and the last within a certain margin.
*/
func findNewEndpointsMarg(array []Grid, start int, end int, shift_amount uint64, query uint64, m_64 uint64) (int, int, int) {
	new_start := binarySearchGridArray(array, start, end, shift_amount, query)
	new_end := end
	if query < 255 {
		new_end = binarySearchGridArray(array, new_start, end, shift_amount, query+1)
	}
	marg_end := new_end
	if query < 255-m_64 {
		marg_end = binarySearchGridArray(array, new_start, end, shift_amount, query+m_64)
	}
	return new_start, new_end, marg_end
}

func removeRedundantGrids(array []Grid, margin float64, tNum int, naphilArray []uint8) []Grid {
	tellTime := false
	startTime := time.Now().Unix()

	arrayLen := len(array)

	/*The margin that is used to determine whether grids stay or go.*/
	margInt := uint8(margin * 256.0)
	m_64 := uint64(margInt)
	margin_signed := int(margInt)

	/*Used in binary searches*/
	x_ := 0
	y_ := arrayLen

	/*Finding where shallow grids (those with lesser differences
	between min-max luma values) end and deep grids (those with
	greater differences) begin.*/
	var rangeCutoff int
	if margInt == 255 {
		rangeCutoff = arrayLen
	} else {
		for x_ < y_ {
			mid := x_ + ((y_ - x_) / 2)
			if array[mid].dimCornAvg>>56 == 0 {
				x_ = mid + 1
			} else {
				y_ = mid
			}
		}
		rangeCutoff = x_
	}

	/*These will store the cross-range (greatest possible difference
	between two pixels in different grids) and the corner that is
	mismatche between two grids.*/
	var crossRange, mis uint8
	/*These will store the product of the area of the grid and margin
	(for the purposes of comparing shallow grids with each other), and
	offsets in the pixel array that grids point to.*/
	var g1_offset int

	/*The dimensions of the first grid.*/
	dims := (array[0].dimCornAvg >> 40) & 0xFFFF

	/*Determining the beginning and end of parallelized subsections of the loop below. The endpoints
	are set to dimension-based boundaries in the array to ensure all grids are compared with similar
	grids. Some possible comparisons would be missed if the loop divisions fell in the middle of
	a subset of grids with equal dimensions.*/
	var loopDivs []int
	if tNum > 1 {
		loopDivs = make([]int, tNum+1)
		loopDivs[0] = 0
		loopDivs[tNum] = rangeCutoff
		for i := 1; i < tNum; i++ {
			tempDiv := i * arrayLen / tNum
			dims := (array[tempDiv].dimCornAvg >> 40) & 0xFFFF
			wTemp := array[tempDiv].getW()
			hTemp := array[tempDiv].getH()
			/*The initial boundary falls in the middle of a subset of gris with equal dimensions.*/
			if (array[tempDiv-1].dimCornAvg>>40)&0xFFFF == dims && (array[tempDiv+1].dimCornAvg>>40)&0xFFFF == dims {
				a := loopDivs[i-1]
				b := max(0, tempDiv-1)
				var m int
				var gTemp Grid

				/*Finnding the first grid that matches the dimensions*/
				for a < b {
					m = a + ((b - a) / 2)
					gTemp = array[m]
					if gTemp.getH() == hTemp && gTemp.getW() == wTemp {
						b = m
					} else {
						a = m + 1
					}
				}
				div1 := a

				/*Finnding the last grid that matches the dimensions*/
				a = min(tempDiv+1, rangeCutoff)
				b = rangeCutoff
				for a < b {
					m = a + ((b - a) / 2)
					if gTemp.getH() == hTemp && gTemp.getW() == wTemp {
						a = m + 1
					} else {
						b = 1
					}
				}
				div2 := a

				/*Choose the beginning or end of this subset depending
				on which is closer to the original estimate*/
				if tempDiv-div1 > div2-tempDiv {
					tempDiv = div2
				} else {
					tempDiv = div1
				}
			}
			loopDivs[i] = tempDiv
		}
	}

	/*This loop is concerned with comparing shallow grids with each other.
	The cross-range calculation procedure and the comparison function is
	different between these and the deep grids, in addition to occupying
	different sections of the array.*/
	wg := sync.WaitGroup{}
	for i__ := range tNum {
		var start, end int
		if tNum > 1 {
			start, end = loopDivs[i__], loopDivs[i__+1]
		} else {
			start, end = 0, rangeCutoff
		}
		wg.Add(1)
		go func(start, end int) {
			defer wg.Done()
			rBits := rand.Uint64()
			i := start
			w_curr := array[start].getW()
			h_curr := array[start].getH()

			/*A signed variable containing the grid's area, used both to determine
			the total allowable difference between two shallow grids and use for
			offsets in the pixel data array.*/
			area_signed := int(w_curr) * int(h_curr)
			areaMarg := area_signed * margin_signed

			x_ := start + 1
			y_ = end
			var gTemp Grid
			for x_ < y_ {
				mid := x_ + ((y_ - x_) / 2)
				gTemp = array[mid]
				if gTemp.getW() != w_curr || gTemp.getH() != h_curr {
					y_ = mid
				} else {
					x_ = mid + 1
				}
			}
			dim_end := x_

			/*Determining the last grids similar to the first grid in various aspects.*/
			_, avg_end, avg_marg_end := findEndpoints(array, 0, 32, dim_end, m_64)
			c1, c1_end, c1_marg_end := findEndpoints(array, 0, 24, avg_end, m_64)
			c2, c2_end, c2_marg_end := findEndpoints(array, 0, 16, c1_end, m_64)
			c3, c3_end, c3_marg_end := findEndpoints(array, 0, 8, c2_end, m_64)
			c4, c4_end, c4_marg_end := findEndpoints(array, 0, 0, c3_end, m_64)

			/*These are used to reset the above values below.*/
			var new_c1_start, new_c1_end, new_c2_start, new_c2_end, new_c3_start, new_c3_end, new_avg_start, new_avg_end, j, new_j int

			var g1 Grid

			var breakLoop bool

		loopStart_shallow:
			if i < end {
				if tellTime && time.Now().Unix() > startTime {
					fmt.Printf("%d	%d\n", i, j)
					startTime = time.Now().Unix()
				}
				/*If a grid is eliminated, its metadata value will have 0xFF placed
				at the highest 16 bits.*/
				if array[i].dimCornAvg>>56 != 255 {
					/*If nothing changes between the dimensions, averages, or corners
					between the previous and current grid, go to the section of code
					where the current grid is compared to subsequent grids. Otherwise,
					change the indices.*/
					if i < c4_end {
						g1 = array[i]
						j = i + 1
						g1_offset = g1.offset
						goto comparison_shallow
					}
					if i >= c3_end {
						if i >= c2_end {
							if i >= c1_end {
								if i >= avg_end {
									if i >= dim_end {
										goto reset_dim_shallow
									}
									goto reset_avg_shallow
								}
								goto reset_c1_shallow
							}
							goto reset_c2_shallow
						}
						goto reset_c3_shallow
					}
					goto reset_c4_shallow
				reset_dim_shallow:
					w_curr = array[i].getW()
					h_curr = array[i].getH()
					area_signed = int(w_curr) * int(h_curr)
					areaMarg = area_signed * margin_signed

					x_ = i + 1
					y_ = end
					/*Find the last grid with dimensions equal to the current one.*/
				binarySearchLoop_shallow:
					if x_ < y_ {
						mid := x_ + ((y_ - x_) / 2)
						gTemp = array[mid]
						if gTemp.getW() == w_curr && gTemp.getH() == h_curr {
							x_ = mid + 1
							goto binarySearchLoop_shallow
						}
						y_ = mid
						goto binarySearchLoop_shallow
					}
					dim_end = x_

					/*Reset the appropriate dimension values accordingly.*/
					area_signed = int(w_curr) * int(h_curr)
					areaMarg = area_signed * margin_signed

					/*Resetting everything else besides dimensions*/
				reset_avg_shallow:
					_, avg_end, avg_marg_end = findEndpoints(array, i, 32, dim_end, m_64)
				reset_c1_shallow:
					c1, c1_end, c1_marg_end = findEndpoints(array, i, 24, avg_end, m_64)
				reset_c2_shallow:
					c2, c2_end, c2_marg_end = findEndpoints(array, i, 16, c1_end, m_64)
				reset_c3_shallow:
					c3, c3_end, c3_marg_end = findEndpoints(array, i, 8, c2_end, m_64)
				reset_c4_shallow:
					c4, c4_end, c4_marg_end = findEndpoints(array, i, 0, c3_end, m_64)

					/*Comparing grids to other grids*/
				comparison_shallow:
					if j < c4_marg_end {
						if tellTime && time.Now().Unix() > startTime {
							fmt.Printf("%d	%d\n", i, j)
							startTime = time.Now().Unix()
						}
						/*If the grid at j has not been eliminated*/
						if array[j].dimCornAvg>>56 != 255 {
							g2 := array[j]
							/*It will actually be fairly common among adjacent shallow grids
							for their metadata variables to have a difference less than the
							margin. If not, however, it checks if there is a significant
							mismatch.*/
							if g2.dimCornAvg-g1.dimCornAvg >= m_64 {
								mis = gridMismatchCorn(g1.dimCornAvg&0xFFFFFFFF, g2.dimCornAvg&0xFFFFFFFF, m_64)
								/*The general algorithm for a mismatch is to find new endpoints
								(including margin) for level above the mismatch, then at the level
								of the mismatch and everthing downstream (excluding margin) before
								stopping at the fourth corner.*/
								if mis != 0 {
									if mis == 1 {
										goto check_1
									} else if mis < 3 {
										goto check_2
									} else if mis < 4 {
										goto check_3
									} else {
										goto check_4
									}
								check_1:
									new_avg_start, new_avg_end, breakLoop = findNewEndpoints(array, i, j, 32, avg_marg_end)
									if breakLoop {
										j = c4_marg_end
										goto increment_shallow
									}
									new_c1_start, new_c1_end, c1_marg_end = findNewEndpointsMarg(array, new_avg_start, new_avg_end, 24, c1, m_64)
									goto skip_2
								check_2:
									new_c1_start, new_c1_end, breakLoop = findNewEndpoints(array, i, j, 24, c1_marg_end)
									if breakLoop {
										j = c4_marg_end
										goto increment_shallow
									}
								skip_2:
									new_c2_start, new_c2_end, c2_marg_end = findNewEndpointsMarg(array, new_c1_start, new_c1_end, 16, c2, m_64)
									goto skip_3
								check_3:
									new_c2_start, new_c2_end, breakLoop = findNewEndpoints(array, i, j, 16, c2_marg_end)
									if breakLoop {
										j = c4_marg_end
										goto increment_shallow
									}
								skip_3:
									new_c3_start, new_c3_end, c3_marg_end = findNewEndpointsMarg(array, new_c2_start, new_c2_end, 8, c3, m_64)
									goto skip4
								check_4:
									new_c3_start, new_c3_end, breakLoop = findNewEndpoints(array, i, j, 8, c3_marg_end)
									if breakLoop {
										j = c4_marg_end
										goto increment_shallow
									}
								skip4:
									new_j = binarySearchGridArray(array, new_c3_start, new_c3_end, 0, c4) - 1
									/*This solved a softlock issue.*/
									if new_j >= j {
										j = new_j
									}
									goto increment_shallow
								}
							}
							/*The algorithm for determining a cross-range (or even deciding
							to calculate one) is as follows:
							If two grids have the same min-max values, then it goes to the
							cointoss, since shallow grids by definition already have a difference
							of min-max values below the margin.
							If the maximum or the minimum between two grids is equal, but not both,
							but both are still within the margin, it goes to the cointoss. If they
							are not necessarily in the margin, the cross range is the difference of
							the shared value and the furthest unshared value.
							Finally, if min-max are both different between the grids, cross-range is
							whichever is the greatest difference between opposite grids.*/
							max1 := g1.maxLuma
							max2 := g2.maxLuma
							min1 := g1.minLuma
							min2 := g2.minLuma
							if min1 == min2 {
								if max1 == max2 {
									goto coinToss_shallow
								}
								if max1-min1 < margInt {
									if max2-min1 < margInt {
										goto coinToss_shallow
									}
									crossRange = max2 - min1
								}
								if max1 > max2 {
									crossRange = max1 - min1
								} else {
									crossRange = max2 - min1
								}
							} else if max1 == max2 {
								if max1-min1 < margInt {
									if max1-min2 < margInt {
										goto coinToss_shallow
									}
									crossRange = max1 - min2
								}
								if min1 < min2 {
									crossRange = max1 - min1
								} else {
									crossRange = max1 - min2
								}
							} else if max2-min1 > max2-min1 {
								crossRange = max2 - min1
							} else {
								crossRange = max2 - min1
							}

							/*If there is a substantial cross-range, and the average difference between pixels in
							the grid is substantial, then both remain.*/
							if crossRange >= margInt {
								/*Check to ensure neither grid has its darkest pixel too much above the brightest of
								the other.*/
								if (max2 < 255-margInt && min1 > max2+margInt) || (max1 < 255-margInt && min2 > max1+margInt) {
									goto increment_shallow
								}

								sum := 0

								/*The above sum, minus the sum of the differences of pixels
								already calculated.*/
								maxSum_diff := areaMarg

								i_1 := g1_offset
								end_1 := g1_offset + area_signed
								end_l := end_1 - (area_signed % 4)
								i_2 := g2.offset
								cr := int(crossRange)
								var diff, p1, p2 uint8
								/*The product of the remaining number of pixels and the
								cross-range between grids.*/
								i_cr := area_signed * cr
								/*The loop ends if the sum of the differences between
								corresponding pixels exceeds the product of the area
								and the margin OR if the sum plus the product of the
								remaining pixels and the cross-range is less than this
								total permitted sum, meaining that it is no longer
								mathetmatically possible for the grids to have such
								a great average distance. This tightrope balance
								fixed a slowdown issue.
								This is unrolled, examining four pixels a cycle.*/
								for i_1 < end_l {
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p2 > p1 {
											diff = p2 - p1
										}
										sum += int(diff)
										maxSum_diff -= int(diff)
									}
									i_cr -= cr
									i_1++
									i_2++
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p2 > p1 {
											diff = p2 - p1
										}
										sum += int(diff)
										maxSum_diff -= int(diff)
									}
									i_cr -= cr
									i_1++
									i_2++
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p2 > p1 {
											diff = p2 - p1
										}
										sum += int(diff)
										maxSum_diff -= int(diff)
									}
									i_cr -= cr
									i_1++
									i_2++
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p2 > p1 {
											diff = p2 - p1
										}
										sum += int(diff)
										maxSum_diff -= int(diff)
									}
									i_cr -= cr
									if sum > areaMarg {
										goto increment_shallow
									}
									if i_cr < maxSum_diff {
										goto coinToss_shallow
									}
									i_1++
									i_2++
								}
								for i_1 < end_1 && i_cr < maxSum_diff {
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p2 > p1 {
											diff = p2 - p1
										}
										sum += int(diff)
										maxSum_diff -= int(diff)
									}
									if sum > areaMarg {
										goto increment_shallow
									}
									i_1++
									i_2++
								}
							}

							/*If the grids are so similar that cross-range is not substantial or the average difference
							is not substantial, randomly decide which stays and which goes.*/
						coinToss_shallow:
							if rBits%2 == 0 {
								array[i].dimCornAvg |= 0xFF00000000000000
								j = c4_marg_end
							} else {
								array[j].dimCornAvg |= 0xFF00000000000000
							}
							/*Instead of randomly generating a number only to use one of its bits each cointoss, a random
							64-bit number is generated at the beginning of the loop, shifted each coinn-toss, and reset
							whenever its bits run out.*/
							rBits >>= 1
							if rBits == 0 {
								rBits = rand.Uint64()
							}
						}
					increment_shallow:
						j++
						goto comparison_shallow
					}
				}
				i++
				goto loopStart_shallow
			}
		}(start, end)
	}
	wg.Wait()
	if tNum > 1 {
		loopDivs = make([]int, tNum+1)
		loopDivs[0] = rangeCutoff
		loopDivs[tNum] = arrayLen
		for i := 1; i < tNum; i++ {
			tempDiv := (i * (arrayLen - rangeCutoff) / tNum) + rangeCutoff
			dims := (array[tempDiv].dimCornAvg >> 40) & 0xFFFF
			if (array[tempDiv-1].dimCornAvg>>40)&0xFFFF == dims && (array[tempDiv+1].dimCornAvg>>40)&0xFFFF == dims {
				a := loopDivs[i-1]
				b := max(tempDiv-1, rangeCutoff)
				var m int
				for a < b {
					m = a + ((b - a) / 2)
					if (array[m].dimCornAvg>>40)&0xFFFF == dims {
						b = m
					} else {
						a = m + 1
					}
				}
				div1 := a
				a = min(tempDiv+1, arrayLen)
				b = arrayLen
				for a < b {
					m = a + ((b - a) / 2)
					if (array[m].dimCornAvg>>40)&0xFFFF == dims {
						a = m + 1
					} else {
						b = 1
					}
				}
				div2 := a
				if tempDiv-div1 > div2-tempDiv {
					tempDiv = div2
				} else {
					tempDiv = div1
				}
			}
			loopDivs[i] = tempDiv
		}
	}
	/*Instead of determining average differences between grids, this checks the single greatest
	difference between corresponding pixels.*/
	wg = sync.WaitGroup{}
	for i__ := range tNum {
		var start, end int
		if tNum > 1 {
			start, end = loopDivs[i__], loopDivs[i__+1]
		} else {
			start, end = rangeCutoff, arrayLen
		}
		wg.Add(1)
		go func(start, end int) {
			defer wg.Done()
			rBits := rand.Uint64()
			i := start
			w_curr := array[start].getW()
			h_curr := array[start].getH()

			area_signed := int(w_curr) * int(h_curr)

			remainder_area := area_signed % 4

			x_ := start + 1
			y_ = end
			var gTemp Grid
			for x_ < y_ {
				mid := x_ + ((y_ - x_) / 2)
				gTemp = array[mid]
				if gTemp.getW() != w_curr || gTemp.getH() != h_curr {
					y_ = mid
				} else {
					x_ = mid + 1
				}
			}
			dim_end := x_

			/*Determining the last grids similar to the first grid in various aspects.*/
			_, avg_end, avg_marg_end := findEndpoints(array, 0, 32, dim_end, m_64)
			c1, c1_end, c1_marg_end := findEndpoints(array, 0, 24, avg_end, m_64)
			c2, c2_end, c2_marg_end := findEndpoints(array, 0, 16, c1_end, m_64)
			c3, c3_end, c3_marg_end := findEndpoints(array, 0, 8, c2_end, m_64)
			c4, c4_end, c4_marg_end := findEndpoints(array, 0, 0, c3_end, m_64)

			/*These are used to reset the above values below.*/
			var new_c1_start, new_c1_end, new_c2_start, new_c2_end, new_c3_start, new_c3_end, new_avg_start, new_avg_end, j, new_j int

			var g1 Grid

			var breakLoop bool
		loopStart_deep:
			if i < end {
				if tellTime && time.Now().Unix() > startTime {
					fmt.Printf("%d	%d\n", i, j)
					startTime = time.Now().Unix()
				}
				if array[i].dimCornAvg>>56 != 255 {
					if i < c4_end {
						g1 = array[i]
						j = i + 1
						goto comparison_deep
					}
					if i >= c3_end {
						if i >= c2_end {
							if i >= c1_end {
								if i >= avg_end {
									if i >= dim_end {
										goto reset_dim_deep
									}
									goto reset_avg_deep
								}
								goto reset_c1_deep
							}
							goto reset_c2_deep
						}
						goto reset_c3_deep
					}
					goto reset_c4_deep
				reset_dim_deep:
					dims = (array[i].dimCornAvg >> 40) & 0xFFFF
					x_ = i + 1
					y_ = end
					for x_ < y_ {
						mid := x_ + ((y_ - x_) / 2)
						gTemp = array[mid]
						if (gTemp.dimCornAvg>>40)&0xFFFF <= dims {
							x_ = mid + 1
						} else {
							y_ = mid
						}
					}
					dim_end = x_
					area_signed = int(dims & 255)
					area_signed *= int((dims >> 8) & 255)
				reset_avg_deep:
					_, avg_end, avg_marg_end = findEndpoints(array, i, 32, dim_end, m_64)
				reset_c1_deep:
					c1, c1_end, c1_marg_end = findEndpoints(array, i, 24, avg_end, m_64)
				reset_c2_deep:
					c2, c2_end, c2_marg_end = findEndpoints(array, i, 16, c1_end, m_64)
				reset_c3_deep:
					c3, c3_end, c3_marg_end = findEndpoints(array, i, 8, c2_end, m_64)
				reset_c4_deep:
					c4, c4_end, c4_marg_end = findEndpoints(array, i, 0, c3_end, m_64)
					if c4_marg_end > arrayLen {
						c4_marg_end = arrayLen
					}
				comparison_deep:
					if j < c4_marg_end {
						if tellTime && time.Now().Unix() > startTime {
							fmt.Printf("%d	%d\n", i, j)
							startTime = time.Now().Unix()
						}
						if array[j].dimCornAvg>>56 != 255 {
							g2 := array[j]
							if g2.dimCornAvg-g1.dimCornAvg >= m_64 {
								mis = gridMismatchCorn(g1.dimCornAvg&0xFFFFFFFF, g2.dimCornAvg&0xFFFFFFFF, m_64)
								if mis != 0 {
									/*The general algorithm for a mismatch is to find new endpoints
									(including margin) for level above the mismatch, then at the level
									of the mismatch and everthing downstream (excluding margin) before
									stopping at the fourth corner.*/
									if mis != 0 {
										if mis == 1 {
											goto check_1
										} else if mis < 3 {
											goto check_2
										} else if mis < 4 {
											goto check_3
										} else {
											goto check_4
										}
									check_1:
										new_avg_start, new_avg_end, breakLoop = findNewEndpoints(array, i, j, 32, avg_marg_end)
										if breakLoop {
											j = c4_marg_end
											goto increment_deep
										}
										new_c1_start, new_c1_end, c1_marg_end = findNewEndpointsMarg(array, new_avg_start, new_avg_end, 24, c1, m_64)
										goto skip_2
									check_2:
										new_c1_start, new_c1_end, breakLoop = findNewEndpoints(array, i, j, 24, c1_marg_end)
										if breakLoop {
											j = c4_marg_end
											goto increment_deep
										}
									skip_2:
										new_c2_start, new_c2_end, c2_marg_end = findNewEndpointsMarg(array, new_c1_start, new_c1_end, 16, c2, m_64)
										goto skip_3
									check_3:
										new_c2_start, new_c2_end, breakLoop = findNewEndpoints(array, i, j, 16, c2_marg_end)
										if breakLoop {
											j = c4_marg_end
											goto increment_deep
										}
									skip_3:
										new_c3_start, new_c3_end, c3_marg_end = findNewEndpointsMarg(array, new_c2_start, new_c2_end, 8, c3, m_64)
										goto skip4
									check_4:
										new_c3_start, new_c3_end, breakLoop = findNewEndpoints(array, i, j, 8, c3_marg_end)
										if breakLoop {
											j = c4_marg_end
											goto increment_deep
										}
									skip4:
										new_j = binarySearchGridArray(array, new_c3_start, new_c3_end, 0, c4) - 1
										if new_j >= j {
											j = new_j
										}
										goto increment_deep
									}
								}
							}
							max1 := g1.maxLuma
							max2 := g2.maxLuma
							min1 := g1.minLuma
							min2 := g2.minLuma
							if min1 == min2 {
								if max1 >= max2 {
									crossRange = max1 - min1
								} else {
									crossRange = max2 - min1
								}
							} else if max1 == max2 {
								if max1 < max2 {
									crossRange = max1 - min1
								} else {
									crossRange = max1 - min2
								}
							} else {
								crossRange = max(max2-min1, max1-min2)
							}

							if crossRange >= margInt {
								var end_l int
								var p1, p2, diff uint8
								end_l = g1_offset + area_signed - remainder_area
								i_1 := g1_offset
								i_2 := g2.offset
								/*This loop is unrolled, checking four pairs of pixels in a cycle.*/
								for i_1 < end_l {
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p1 < p2 {
											diff = p2 - p1
										}
										if diff >= margInt {
											goto increment_deep
										}
									}
									i_1++
									i_2++
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p1 < p2 {
											diff = p2 - p1
										}
										if diff >= margInt {
											goto increment_deep
										}
									}
									i_1++
									i_2++
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p1 < p2 {
											diff = p2 - p1
										}
										if diff >= margInt {
											goto increment_deep
										}
									}
									i_1++
									i_2++
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p1 < p2 {
											diff = p2 - p1
										}
										if diff >= margInt {
											goto increment_deep
										}
									}
									i_1++
									i_2++
								}
								if remainder_area != 0 {
									p1 = naphilArray[i_1]
									p2 = naphilArray[i_2]
									if p1 != p2 {
										diff = p1 - p2
										if p1 < p2 {
											diff = p2 - p1
										}
										if diff >= margInt {
											goto increment_deep
										}
									}
									if remainder_area > 1 {
										i_1++
										i_2++
										p1 = naphilArray[i_1]
										p2 = naphilArray[i_2]
										if p1 != p2 {
											diff = p1 - p2
											if p1 < p2 {
												diff = p2 - p1
											}
											if diff >= margInt {
												goto increment_deep
											}
										}
										if remainder_area > 2 {
											i_1++
											i_2++
											p1 = naphilArray[i_1]
											p2 = naphilArray[i_2]
											if p1 != p2 {
												diff = p1 - p2
												if p1 < p2 {
													diff = p2 - p1
												}
												if diff >= margInt {
													goto increment_deep
												}
											}
										}
									}
								}
							}

							if rBits%2 == 0 {
								array[i].dimCornAvg |= 0xFF00000000000000
								j = c4_marg_end
							} else {
								array[j].dimCornAvg |= 0xFF00000000000000
							}
							rBits >>= 1
							if rBits == 0 {
								rBits = rand.Uint64()
							}
						}
					increment_deep:
						j++
						goto comparison_deep
					}
				}
				i++
				goto loopStart_deep
			}
		}(start, end)
	}
	wg.Wait()

	var max_64 uint64
	max_64 = math.MaxUint64

	eliminated_shallow_64 := uint64(0)
	for i := range rangeCutoff {
		eliminated_shallow_64 += ((array[i].dimCornAvg >> 56) / 255)
	}
	remaining_shallow := rangeCutoff - int(eliminated_shallow_64)
	resettled_shallow := 0
	var i = 0
	var j int
	/*These loops "yanks" all remaining grids towards the front*/
	for i < rangeCutoff-1 && resettled_shallow < remaining_shallow {
		if array[i].dimCornAvg>>56 != 255 {
			i++
		} else if j < i {
			j = i + 1
		} else if array[j].dimCornAvg>>56 == 255 {
			j++
		} else {
			array[i].w__ = array[j].w__
			array[i].h__ = array[j].h__
			array[i].offset = array[j].offset
			array[i].avgLuma = array[j].avgLuma
			array[i].minLuma = array[j].minLuma
			array[i].maxLuma = array[j].maxLuma
			array[i].coord = array[j].coord
			array[i].dimCornAvg = array[j].dimCornAvg
			array[j].dimCornAvg = max_64
			resettled_shallow++
			i++
			j++
		}
	}

	eliminated_deep_64 := uint64(0)
	for i := rangeCutoff; i < arrayLen; i++ {
		eliminated_deep_64 += ((array[i].dimCornAvg >> 56) / 255)
	}
	remaining_deep := arrayLen - rangeCutoff - int(eliminated_deep_64)
	resettled_deep := 0
	j = rangeCutoff
	for i < arrayLen-1 && resettled_deep < remaining_deep {
		if array[i].dimCornAvg>>56 != 255 {
			i++
		} else if j < i {
			j = i + 1
		} else if array[j].dimCornAvg>>56 == 255 {
			j++
		} else {
			array[i].w__ = array[j].w__
			array[i].h__ = array[j].h__
			array[i].offset = array[j].offset
			array[i].avgLuma = array[j].avgLuma
			array[i].minLuma = array[j].minLuma
			array[i].maxLuma = array[j].maxLuma
			array[i].coord = array[j].coord
			array[i].dimCornAvg = array[j].dimCornAvg
			array[j].dimCornAvg = max_64
			resettled_deep++
			i++
			j++
		}
	}
	/*This erases all eliminated grids*/
	array = array[:resettled_deep+resettled_shallow]

	return array
}

/*
Get the xy coordinates from a tree in order to
create grids.
*/
func coordsFromTree(t *Tree, imageIndex uint64, coordArray [][]uint64, index int, reuse []uint64) {
	/*If the tree is in fact a leaf, it place its
	coordinates into the array*/
	if t.hasChildren == 0 {
		if index >= len(coordArray) {
			panic("Out of bounds")
		}
		if coordArray[index] != nil && len(coordArray[index]) != 0 {
			panic("Already set\n")
		}
		reuse[0] = t.x1
		reuse[1] = t.x2
		reuse[2] = t.y1
		reuse[3] = t.y2
		reuse[4] = imageIndex
		coordArray[index] = make([]uint64, 5)
		copy(coordArray[index], reuse)
		return
	}
	/*Otherwise, find leaves while offsetting the index when
	appropriate.*/
	if t.hasChildren&1 != 0 {
		coordsFromTree(t.rTree, imageIndex, coordArray, index, reuse)
	}
	if (t.hasChildren)&2 != 0 {
		coordsFromTree(t.lTree, imageIndex, coordArray, index+t.rTree.leafNum, reuse)
	}
}

func encodeCoords(t *Tree, imageIndex uint64, encodedCoords []uint64, index int) {
	/*If the tree is in fact a leaf, it place its
	coordinates into the array*/
	if t.hasChildren == 0 {
		if index >= len(encodedCoords) {
			panic("Out of bounds")
		}
		if encodedCoords[index] != 0 {
			panic("Already set\n")
		}
		/*Encode the index of the image from the array*/
		enc := imageIndex
		/*Encode the width*/
		enc <<= 8
		enc += ((t.x2 - t.x1) & 255)
		/*Encode the height*/
		enc <<= 8
		enc += ((t.y2 - t.y1) & 255)
		enc <<= 13
		/*Encode the leftmost x-coordinate*/
		if t.x1 > 8191 {
			panic("Invalid coordinate")
		}
		enc += ((^t.x1) & 8191)
		/*Encode the top y-coordinate*/
		enc <<= 13
		if t.y1 > 8191 {
			panic("Invalid coordinate")
		}
		enc += ((^t.y1) & 8191)
		encodedCoords[index] = enc
		return
	}
	/*Otherwise, find leaves while offsetting the index when
	appropriate.*/
	if t.hasChildren&1 != 0 {
		encodeCoords(t.rTree, imageIndex, encodedCoords, index)
	}
	if (t.hasChildren)&2 != 0 {
		encodeCoords(t.lTree, imageIndex, encodedCoords, index+t.rTree.leafNum)
	}
}

func lumaTrace(imgW int, imgH int, pix_data []uint8, array []Grid, arrayLen int, t *Tree, naphilArrayIn []uint8) []uint8 {
	tellTime := false

	/*Initialize array to store the output data*/
	pix_data_out := make([]uint8, imgW*imgH)

	/*Create an array of coordinates based off the tree*/
	coordArray := make([][]uint64, t.leafNum)

	reuse := make([]uint64, 5)
	l := t.leafNum
	coordsFromTree(t, 0, coordArray, 0, reuse)

	/*Sort the coordinates*/
	sort.Slice(coordArray, func(i, j int) bool {
		return coordArray[i][1]-coordArray[i][0] < coordArray[j][1]-coordArray[j][0] || (coordArray[i][1]-coordArray[i][0] == coordArray[j][1]-coordArray[j][0] && coordArray[i][3]-coordArray[i][2] < coordArray[j][3]-coordArray[j][2])
	})

	/*Create an array of indices to a naphil array*/
	tempIndex := 0

	indexArray := make([]int, l)

	i_ := 0

	var startTemp int64
	if tellTime {
		startTemp = time.Now().Unix()
	}

	/*Populate the index array*/
	for i_ < l {
		if tellTime && time.Now().Unix() > startTemp {
			fmt.Printf("Setting index values	%f%%\n", 100.0*float64(i_)/float64(l))
			startTemp = time.Now().Unix()
		}
		area := int(coordArray[i_][1]-coordArray[i_][0]) * int(coordArray[i_][3]-coordArray[i_][2])
		a := i_ + 1
		b := l
		for a < b {
			m := a + ((b - a) / 2)
			if coordArray[m][1]-coordArray[m][0] == coordArray[i_][1]-coordArray[i_][0] && coordArray[m][3]-coordArray[m][2] == coordArray[i_][3]-coordArray[i_][2] {
				a = m + 1
			} else {
				b = m
			}
		}
		z := a
		j_ := i_
		for j_ < z {
			indexArray[j_] = tempIndex
			tempIndex += area
			j_++
		}
		i_ = z
	}

	/*Create the naphil array which will store the same data as pix_data
	in a different arrangement, grid-by-grid.*/
	naphilArrayTrace := make([]uint8, imgW*imgH)

	/*Array of grids from the iamge*/
	coordinatedArray := make([]Grid, l)

	if tellTime {
		startTemp = time.Now().Unix()
	}
	/*Populate the grid array*/
	for i := range l {
		if tellTime && time.Now().Unix() > startTemp {
			fmt.Printf("Generating grids in traced image	%f%%\n", 100.0*float64(i_)/float64(l))
			startTemp = time.Now().Unix()
		}

		/*Gather the coordinates, calculate dimensions*/
		ca := coordArray[i]
		x1 := ca[0]
		x2 := ca[1]
		y1 := ca[2]
		y2 := ca[3]
		gw := int(x2 - x1)
		gh := int(y2 - y1)
		area := gw * gh

		/*Get offset data*/
		offset := indexArray[i]

		/*Place the proper data into the naphil array*/
		populateNaphil(naphilArrayTrace, pix_data, x1, x2, y1, y2, offset, uint64(imgW))

		/*Get the minimum, maximum, and sum of the pixels in the grid*/
		sum := uint64(0)
		j := offset
		end := offset + area
		maxLuma := slices.Max(naphilArrayTrace[offset:end])
		minLuma := slices.Min(naphilArrayTrace[offset:end])
		for j < end {
			sum += uint64(naphilArrayTrace[j])
			j++
		}

		dimCornAvg := uint64(0)
		dimCornAvg += uint64(gw)
		dimCornAvg <<= 8
		dimCornAvg += uint64(gh)
		dimCornAvg <<= 8
		dimCornAvg += (sum / uint64(area))
		dimCornAvg <<= 8
		dimCornAvg += uint64(maxLuma - minLuma)
		dimCornAvg <<= 8
		dimCornAvg += uint64(maxLuma)
		dimCornAvg <<= 16
		coordinatedArray[i] = Grid{
			w__:        uint8(gw),
			h__:        uint8(gh),
			avgLuma:    uint8(sum / uint64(area)),
			minLuma:    minLuma,
			maxLuma:    maxLuma,
			dimCornAvg: dimCornAvg,
			coord:      (uint64(y1) << 13) + uint64(x1),
			offset:     offset,
		}
	}

	/*Sort the grids*/
	i_ = 0

	if tellTime {
		startTemp = time.Now().Unix()
	}
	for i_ < l {
		if tellTime && time.Now().Unix() > startTemp {
			fmt.Printf("Sorting grids	%f%%\n", 100.0*float64(i_)/float64(l))
			startTemp = time.Now().Unix()
		}

		a := i_ + 1
		b := l
		for a < b {
			m := a + ((b - a) / 2)
			if coordinatedArray[m].getW() == coordinatedArray[i_].getW() && coordinatedArray[m].getH() == coordinatedArray[i_].getH() {
				a = m + 1
			} else {
				b = m
			}
		}
		sort.Slice(coordinatedArray[i_:a], func(i, j int) bool {
			return coordinatedArray[i_+i].dimCornAvg < coordinatedArray[i_+j].dimCornAvg
		})
		i_ = a
	}

	dim_cursor := 0
	dim_start_data := 0

	var gridLoopTime int64
	if tellTime {
		gridLoopTime = time.Now().Unix()
	}
	/*Start the trace, grid-by-grids*/
	for dim_cursor < l {
		/*Dimensions of the grid at the current cursor*/
		gw := coordinatedArray[dim_cursor].getW()
		gh := coordinatedArray[dim_cursor].getH()
		area := int(gw) * int(gh)
		area_32 := uint32(area)

		/*The last grid with the same dimensions*/
		a := dim_cursor
		b := l
		if tellTime {
			startTemp = time.Now().Unix()
		}
		for a < b {
			if tellTime && time.Now().Unix() > startTemp {
				fmt.Printf("Setting boundaries based on dimensions	%f%%\n", 100.0*float64(l-(a*b))/float64(l))
				startTemp = time.Now().Unix()
			}
			m := a + ((b - a) / 2)
			if coordinatedArray[m].getW() == gw && coordinatedArray[m].getH() == gh {
				a = m + 1
			} else {
				b = m
			}
		}
		dim_end := a

		/*The last grid with the same dimensions from the dataset*/
		a = dim_start_data
		b = arrayLen
		if tellTime {
			startTemp = time.Now().Unix()
		}
		for a < b {
			if tellTime && time.Now().Unix() > startTemp {
				fmt.Printf("Setting boundaries based on dimensions	%f%%\n", 100.0*float64(arrayLen-(a*b))/float64(arrayLen))
				startTemp = time.Now().Unix()
			}
			m := a + ((b - a) / 2)
			if array[m].getW() == gw && array[m].getH() == gh {
				a = m + 1
			} else {
				b = m
			}
		}
		dim_end_data := a

		i := dim_cursor
		for i < dim_end {
			if tellTime && time.Now().Unix() > gridLoopTime+10 {
				fmt.Printf("Matching grids	%f%%\n", 100.0*float64(i)/float64(l))
				gridLoopTime = time.Now().Unix()
			}
			/*Getting the offset of the grid and its pixels*/
			g := coordinatedArray[i]
			g_offset := g.offset
			g_offset_end := g_offset + area
			g_min := g.minLuma
			g_max := g.maxLuma

			/*The first and last grids in the dataset with
			identical metadata (if any)*/
			a := dim_start_data
			b := dim_end_data
			var start, end int
			for a < b {
				m := a + ((b - a) / 2)
				if array[m].dimCornAvg < g.dimCornAvg {
					a = m + 1
				} else {
					b = m
				}
			}
			start = a
			b = dim_end_data
			for a < b {
				m := a + ((b - a) / 2)
				if array[m].dimCornAvg > g.dimCornAvg {
					b = m
				} else {
					a = m + 1
				}
			}
			end = a

			var minDiff_8, g_avg uint8
			var minDiffC int
			var p Grid
			j := start

			/*If there are data grids with identical metadata to the
			trace grid, compare them.*/
			minDiff_32 := 255 * area_32
			if start != end {
				for j < end {
					if tellTime && time.Now().Unix() > startTemp {
						fmt.Printf("Looking for best match among similar grids	%f%%\n", 100.0*float64(j-start)/float64(end-start))
						startTemp = time.Now().Unix()
					}
					p = array[j]
					diffTemp := gridDiffNaphil(p, minDiff_32, naphilArrayIn, naphilArrayTrace, area, g_min, g_max, g_offset, g_offset_end)
					if diffTemp < minDiff_32 {
						minDiff_32 = diffTemp
						minDiffC = j
						if minDiff_32 == 0 {
							break
						}
					}
					j++
				}
			}
			g_avg = g.avgLuma
			minDiff_8 = uint8(minDiff_32 / area_32)
			var avg_end, avg_start int
			var diffTemp_32 uint32
			/*If there are data grids with larger ranges but are
			still potentially similar to the trace grids, compare them.*/
			if end < dim_end_data {
				/*Check for the last of these.*/
				if minDiff_8 != 255 && g_avg < 255-minDiff_8 {
					a = end
					b = dim_end_data
					for a < b {
						m := a + ((b - a) / 2)
						if array[m].avgLuma > g_avg+minDiff_8 {
							b = m
						} else {
							a = m + 1
						}
					}
					avg_end = a
				} else {
					avg_end = dim_end_data
				}
				j = end
				for j < avg_end {
					if tellTime && time.Now().Unix() > startTemp {
						fmt.Printf("Looking for best match among similar grids with higher chromatic diversity	%f%%\n", 100.0*float64(j-end)/float64(avg_end-end))
						startTemp = time.Now().Unix()
					}
					p = array[j]
					diffTemp_32 = gridDiffNaphil(p, minDiff_32, naphilArrayIn, naphilArrayTrace, area, g_min, g_max, g_offset, g_offset_end)
					/*Every time a more similar grid is found, restrict the search.*/
					if diffTemp_32 < minDiff_32 {
						minDiff_32 = diffTemp_32
						minDiffC = j
						tempDiff := uint8(minDiff_32 / area_32)
						if tempDiff < minDiff_8 {
							minDiff_8 = tempDiff
							if g_avg < 255-minDiff_8 && j+1 < avg_end {
								a = j + 1
								b = avg_end
								for a < b {
									m := a + ((b - a) / 2)
									if array[m].avgLuma >= g_avg+minDiff_8 {
										b = m
									} else {
										a = m + 1
									}
								}
								avg_end = a
							}
						}
					}
					j++

				}
			}
			/*Peform similarly for grids with lower ranges*/
			if start > dim_start_data {
				if minDiff_8 != 255 && g_avg > minDiff_8 {
					a = dim_start_data
					b = start
					for a < b {
						m := a + ((b - a) / 2)
						if array[m].avgLuma >= g_avg-minDiff_8 {
							b = m
						} else {
							a = m + 1
						}
					}
					avg_start = a
				} else {
					avg_start = dim_start_data
				}
				j = start - 1
				for j >= avg_start {
					if tellTime && time.Now().Unix() > startTemp {
						fmt.Printf("Looking for best match among similar grids with higher chromatic diversity	%f%%\n", 100.0*float64(j-end)/float64(avg_end-end))
						startTemp = time.Now().Unix()
					}
					p = array[j]
					diffTemp_32 = gridDiffNaphil(p, minDiff_32, naphilArrayIn, naphilArrayTrace, area, g_min, g_max, g_offset, g_offset_end)

					if diffTemp_32 < minDiff_32 {
						minDiff_32 = diffTemp_32
						minDiffC = j
						tempDiff := uint8(minDiff_32 / area_32)
						if tempDiff < minDiff_8 {
							minDiff_8 = tempDiff
							if g_avg > minDiff_8 && j-1 > avg_start {
								a = avg_start
								b = j - 1
								for a < b {
									m := a + ((b - a) / 2)
									if array[m].avgLuma >= g_avg-minDiff_8 {
										b = m
									} else {
										a = m + 1
									}
								}
								avg_end = a
							}
						}
					}
					j--

				}
			}

			w_signed := int(gw)

			x1 := int(g.coord & 8191)
			x2 := x1 + w_signed
			y1 := int((g.coord >> 13) & 8191)
			y2 := y1 + int(gh)

			kOffset := array[minDiffC].offset

			y := y1
			y_offset := 0
			if tellTime {
				startTemp = math.MaxInt64
			}
			/*Trace this grid's segment of the image.*/
			for y < y2 {
				if tellTime && time.Now().Unix() > startTemp {
					fmt.Printf("Populating the output pixel data	%f%%\n", 100.0*float64(y-y1)/float64(y2-y1))
					startTemp = time.Now().Unix()
				}
				offset_n := kOffset + (y_offset * w_signed)
				offset_p := (y * imgW)
				end := offset_p + x2
				offset_p += x1
				if offset_n >= len(naphilArrayIn) || offset_n+w_signed > len(naphilArrayIn) {
					panic("Out of bounds")
				}
				seq := naphilArrayIn[offset_n : offset_n+w_signed]
				if offset_p >= len(pix_data_out) || end > len(pix_data_out) {
					panic("Out of bounds")
				}
				copy(pix_data_out[offset_p:end], seq)
				y++
				y_offset++
			}

			i++
		}
		dim_cursor = dim_end
		dim_start_data = dim_end_data
	}

	return pix_data_out
}

/*Read a grid array from a file.*/
func readFromFile(fName string) ([]Grid, []uint8, error) {
	var maxLuma, minLuma uint8
	f, err := os.Open(fName)
	if nil != err {
		fmt.Println(err)
		return nil, nil, err
	}
	defer f.Close()

	fStat, err := f.Stat()
	if err != nil {
		panic("Error getting statistical information of file")
	}
	fileSize := fStat.Size()

	reader := bufio.NewReader(f)

	naphilArray := make([]uint8, fileSize)

	_, err = io.ReadFull(reader, naphilArray)
	if nil != err {
		fmt.Println(err)
		return nil, nil, err
	}

	var size uint64

	/*Determine the number of grids in the file*/
	size = 0
	for i := 5; i != 0; i-- {
		size = (size << 8) | uint64(naphilArray[i])
	}

	array := make([]Grid, int(size))

	nCursor := 6

	var w, h uint8
	var w_signed, h_signed, area int
	var dimCornAvg, sum, area_64 uint64
	for i := range size {

		/*Set the dimensions of the grid*/
		w = naphilArray[nCursor]
		nCursor++
		h = naphilArray[nCursor]
		nCursor++
		w_signed = int(w)
		h_signed = int(h)
		area = w_signed * h_signed
		area_64 = uint64(area)
		if w == 0 || h == 0 {
			panic("Empty grid found while reading from file")
		}

		/*Find the minimum, maximum, and sum of the pixel values of the grid*/
		minMaxSum_result := minMaxSum(naphilArray, nCursor, nCursor+area, 255, 0)
		sum = minMaxSum_result & 0xFFFFFF
		minMaxSum_result >>= 24
		minLuma = uint8(minMaxSum_result & 0xFF)
		minMaxSum_result >>= 8
		maxLuma = uint8(minMaxSum_result & 0xFF)

		/*Set the metadata for the grid*/
		dimCornAvg = uint64(w)
		dimCornAvg <<= 8
		dimCornAvg += uint64(h)
		dimCornAvg <<= 8
		dimCornAvg += (sum / area_64)
		dimCornAvg <<= 8
		dimCornAvg += uint64(naphilArray[nCursor])
		dimCornAvg <<= 8
		dimCornAvg += uint64(naphilArray[nCursor+w_signed-1])
		dimCornAvg <<= 8
		dimCornAvg += uint64(naphilArray[nCursor+area-w_signed])
		dimCornAvg <<= 8
		dimCornAvg += uint64(naphilArray[nCursor+area-1])
		array[i] = Grid{
			w__:        w,
			h__:        h,
			avgLuma:    uint8(sum / area_64),
			maxLuma:    maxLuma,
			minLuma:    minLuma,
			offset:     nCursor,
			dimCornAvg: dimCornAvg,
		}
		nCursor += area

	}
	return array, naphilArray, nil
}

/*Write the grid array to a file.*/
func writeToFile(array []Grid, arrayLen int, fName string, naphilArray []uint8) error {
	/*Predefining array size to reduce garbage collection time*/
	byte_array_len := len(naphilArray) + (2 * arrayLen) + 6
	byte_array := make([]byte, byte_array_len)
	naphil_len := len(naphilArray)
	/*Write the size of the array as a little-endian byte array.*/
	for i := range 6 {
		c := uint8((arrayLen >> (8 * i)) % 256)
		byte_array[i] = byte(c)
	}
	cursor := 6
	/*Write the dimensions of each grid, followed by its pixels*/
	for i := 0; i < arrayLen && cursor < byte_array_len; i++ {
		if array[i].getW() == 0 || array[i].getH() == 0 {
			panic("Empty grid found while writing to file")
		}
		a_offset := array[i].offset
		w_ := array[i].getW()
		h_ := array[i].getH()
		byte_array[cursor] = w_
		cursor++
		byte_array[cursor] = byte(array[i].getH())
		cursor++
		h_signed := int(h_)
		w_signed := int(w_)
		area := h_signed * w_signed
		if cursor >= byte_array_len || cursor+area > byte_array_len {
			panic("Out of bounds: byte_array")
		}
		if a_offset >= naphil_len || a_offset+area > naphil_len {
			panic("Out of bonuds: naphilArray")
		}
		copy(byte_array[cursor:cursor+area], naphilArray[a_offset:a_offset+area])
		cursor = min(cursor+area, byte_array_len)
	}
	return os.WriteFile(fName, byte_array[:cursor], 0777)
}

/*Sort a grid array by its metadata, in parallel*/
func parallelSort(array []Grid, tNum int) {
	if tNum > 1 && len(array) > 65535 {
		n := len(array)
		var wg sync.WaitGroup
		size := n / tNum
		for i := range int(tNum) {
			start, end := i*size, (i+1)*size
			if i == tNum-1 {
				end = n
			}
			wg.Add(1)
			go func(start, end int) {
				defer wg.Done()
				sort.Slice(array[start:end], func(i, j int) bool {
					return array[start+i].dimCornAvg < array[start+j].dimCornAvg
				})
			}(start, end)
		}
		wg.Wait()
	}

	sort.Slice(array, func(i, j int) bool {
		return array[i].dimCornAvg < array[j].dimCornAvg
	})
}

/*Combine two arrays*/
func combineArrays(array1 []Grid, array2 []Grid, margin float64, tNum int, naphilArray1 []uint8, naphilArray2 []uint8) ([]Grid, []uint8, int) {
	arrayLen_1 := len(array1)
	arrayLen_2 := len(array2)
	arrayMergedLen := arrayLen_1 + arrayLen_2
	arrayMerged := make([]Grid, arrayMergedLen)
	i_ := 0
	/*The total size of the naphilArray containing the pixel data of both arrays*/
	naphilMergedSize := 0
	bound_1 := arrayLen_1
	/*The size is calculate differently if either array is sorted by range.
	Both methods use binary searches to determine the total size.*/
	if array1[arrayLen_1-1].dimCornAvg>>56 != 0 {
		a_ := 0
		b_ := len(array1)
		for a_ < b_ {
			m := a_ + ((b_ - a_) / 2)
			if array1[m].dimCornAvg>>56 == 0 {
				a_ = m + 1
			} else {
				b_ = m
			}
		}
		i_ = a_
		bound_1 = a_
		for i_ < arrayLen_1 {
			w_ := array1[i_].getW()
			h_ := array1[i_].getH()
			a := i_
			b := arrayLen_1
			for a < b {
				m := a + ((b - a) / 2)
				if array1[m].getW() == w_ && array1[m].getH() == h_ {
					a = m + 1
				} else {
					b = m
				}
			}
			naphilMergedSize += ((a - i_) * int(w_) * int(h_))
			i_ = a
		}
		i_ = 0
	}
	for i_ < bound_1 {
		w_ := array1[i_].getW()
		h_ := array1[i_].getH()
		a := i_
		b := bound_1
		for a < b {
			m := a + ((b - a) / 2)
			if array1[m].getW() == w_ && array1[m].getH() == h_ {
				a = m + 1
			} else {
				b = m
			}
		}
		naphilMergedSize += ((a - i_) * int(w_) * int(h_))
		i_ = a
	}
	bound_2 := arrayLen_2
	if array2[arrayLen_2-1].dimCornAvg>>56 != 0 {
		a_ := 0
		b_ := len(array2)
		for a_ < b_ {
			m := a_ + ((b_ - a_) / 2)
			if array2[m].dimCornAvg>>56 == 0 {
				a_ = m + 1
			} else {
				b_ = m
			}
		}
		i_ = a_
		bound_2 = a_
		for i_ < arrayLen_2 {
			w_ := array2[i_].getW()
			h_ := array2[i_].getH()
			a := i_
			b := arrayLen_2
			for a < b {
				m := a + ((b - a) / 2)
				if array2[m].getW() == w_ && array2[m].getH() == h_ {
					a = m + 1
				} else {
					b = m
				}
			}
			naphilMergedSize += ((a - i_) * int(w_) * int(h_))
			i_ = a
		}
	}
	i_ = 0
	for i_ < bound_2 {
		w_ := array2[i_].getW()
		h_ := array2[i_].getH()
		a := i_
		b := bound_2
		for a < b {
			m := a + ((b - a) / 2)
			if array2[m].getW() == w_ && array2[m].getH() == h_ {
				a = m + 1
			} else {
				b = m
			}
		}
		naphilMergedSize += ((a - i_) * int(w_) * int(h_))
		i_ = a
	}
	naphilMerged := make([]uint8, naphilMergedSize)
	i_ = 0
	j_ := 0
	k_ := 0
	offset_ := 0
	g_1 := array1[i_]
	g_2 := array2[j_]
	var area int
	/*Determining which grid goes in which spot is reminiscent of the end of a
	merge sort. It looks for the lowest of these, then places it into the combined
	array, until it has exhausted one of the arrays.*/
doubleLoopStart:
	if g_1.dimCornAvg < g_2.dimCornAvg {
		arrayMerged[k_] = g_1
		arrayMerged[k_].offset = offset_
		area = (int(g_1.getW()) * int(g_1.getH()))
		copy(naphilMerged[offset_:offset_+area], naphilArray1[g_1.offset:g_1.offset+area])
		offset_ += area
		i_++
		k_++
		if i_ < arrayLen_1 {
			g_1 = array1[i_]
			goto doubleLoopStart
		}
		goto doubleLoopEnd
	}
	arrayMerged[k_] = g_2
	arrayMerged[k_].offset = offset_
	area = (int(g_2.getW()) * int(g_2.getH()))
	copy(naphilMerged[offset_:offset_+area], naphilArray2[g_2.offset:g_2.offset+area])
	offset_ += area
	j_++
	k_++
	if j_ < arrayLen_2 {
		g_2 = array2[j_]
		goto doubleLoopStart
	}
	/*If any in array 1 remain*/
	for i_ < arrayLen_1 {
		g_1 = array1[i_]
		arrayMerged[k_] = g_1
		arrayMerged[k_].offset = offset_
		area := (int(g_1.getW()) * int(g_1.getH()))
		copy(naphilMerged[offset_:offset_+area], naphilArray1[g_1.offset:g_1.offset+area])
		offset_ += area
		i_++
		k_++
	}
	/*If any in array 2 remain*/
doubleLoopEnd:
	for j_ < arrayLen_2 {
		g_2 = array2[j_]
		arrayMerged[k_] = g_2
		arrayMerged[k_].offset = offset_
		area := (int(g_2.getW()) * int(g_2.getH()))
		copy(naphilMerged[offset_:offset_+area], naphilArray2[g_2.offset:g_2.offset+area])
		offset_ += area
		j_++
		k_++
	}
	arrayMerged = removeRedundantGrids(arrayMerged, margin, tNum, naphilMerged)
	return arrayMerged, naphilMerged, len(arrayMerged)
}

/*Generate an image object from an image file.*/
func openImage(path string) (image.Image, error) {
	f, err := os.Open(path)
	if err != nil {
		fmt.Println(err)
		return nil, err
	}
	defer f.Close()
	/*Handle PNG files specially, for reasons I cannot ascertain.*/
	if strings.HasSuffix(strings.ToLower(path), ".png") {
		pngImg, err := fastpng.Decode(f)
		if err != nil {
			log.Fatal(err)
			return nil, err
		}
		return pngImg, err
	}
	img, _, err := image.Decode(f)
	if err != nil {
		fmt.Println("Decoding error: ", err.Error())
		return nil, err
	}
	return img, nil
}

/*Print a time span in human-readable format.*/
func printTime(t int64) {
	if t > 1000000000 {
		sc := int(t / 1000000000)
		if 60 <= sc {
			mn := int(sc / 60)
			sc %= 60
			if 60 <= mn {
				hr := int(mn / 60)
				mn %= 60
				fmt.Printf("%d hours ", hr)
			}
			fmt.Printf("%d minutes ", mn)
		}
		fmt.Printf("%d seconds\n", sc)
	} else if 1000000 <= t {
		fmt.Printf("%d milliseconds\n", t/1000000)
	} else if 1000 <= t {
		fmt.Printf("%d microseconds\n", t/1000)
	} else {
		fmt.Printf("%d nanoseconds\n", t)
	}
}

/*Populate a naphil array*/
func populateNaphil(naphilArray []uint8, pix_data []uint8, x1 uint64, x2 uint64, y1 uint64, y2 uint64, offset int, imgW uint64) {
	w64 := x2 - x1
	w_signed := int(w64)
	y_16 := y1
	y_64 := uint64(0)
	y_signed := 0
	y_offset := y1
	for y_16 < y2 {
		offset_n := offset + (y_signed * w_signed)
		offset_p := y_offset * imgW
		end := offset_p + x2
		offset_p += x1
		copy(naphilArray[offset_n:offset_n+w_signed], pix_data[offset_p:end])
		y_16++
		y_64++
		y_offset++
		y_signed++
	}
}

/*Determines the sum of a subset of a naphil, and nothing else*/
func sumNaphil(naphilArray []uint8, a int, b int) uint64 {
	i := a
	sum := uint64(0)
	for i < b {
		sum += uint64(naphilArray[i])
		i++
		if i >= b {
			break
		}
		sum += uint64(naphilArray[i])
		i++
		if i >= b {
			break
		}
		sum += uint64(naphilArray[i])
		i++
		if i >= b {
			break
		}
		sum += uint64(naphilArray[i])
		i++
	}
	return sum
}

/*
Determines the highest and lowest values in a subset of a naphil, but
stops checking for highest if it finds 255 and lowest if 0. It calculates
the sum all the while.
*/
func minMaxSum(naphilArray []uint8, a int, b int, minLuma uint8, maxLuma uint8) uint64 {
	i := a
	sum := uint64(0)
	var p uint8
	if minLuma != 0 && maxLuma != 255 {
		for i < b {
			p = naphilArray[i]
			sum += uint64(p)
			if p > maxLuma {
				maxLuma = p
			}
			if p < minLuma {
				minLuma = p
			}
			i++
			if i >= b {
				break
			}
			p = naphilArray[i]
			sum += uint64(p)
			if p > maxLuma {
				maxLuma = p
			}
			if p < minLuma {
				minLuma = p
			}
			i++
			if i >= b {
				break
			}
			p = naphilArray[i]
			sum += uint64(p)
			if p > maxLuma {
				maxLuma = p
			}
			if p < minLuma {
				minLuma = p
			}
			i++
			if i >= b {
				break
			}
			p = naphilArray[i]
			sum += uint64(p)
			if p > maxLuma {
				maxLuma = p
			}
			if p < minLuma {
				minLuma = p
			}
			i++
			if maxLuma == 255 || minLuma == 0 {
				break
			}
		}
	}
	if i < b {
		if maxLuma == 255 {
			for i < b {
				p = naphilArray[i]
				sum += uint64(p)
				if p < minLuma {
					minLuma = p
				}
				i++
				if i >= b {
					break
				}
				p = naphilArray[i]
				sum += uint64(p)
				if p < minLuma {
					minLuma = p
				}
				i++
				if i >= b {
					break
				}
				p = naphilArray[i]
				sum += uint64(p)
				if p < minLuma {
					minLuma = p
				}
				i++
				if i >= b {
					break
				}
				p = naphilArray[i]
				sum += uint64(p)
				if p < minLuma {
					minLuma = p
				}
				i++
				if minLuma == 0 {
					break
				}
			}
		} else if minLuma == 0 {
			for i < b {
				p = naphilArray[i]
				sum += uint64(p)
				if p > maxLuma {
					maxLuma = p
				}
				i++
				if i >= b {
					break
				}
				p = naphilArray[i]
				sum += uint64(p)
				if p > maxLuma {
					maxLuma = p
				}
				i++
				if i >= b {
					break
				}
				p = naphilArray[i]
				sum += uint64(p)
				if p > maxLuma {
					maxLuma = p
				}
				i++
				if i >= b {
					break
				}
				p = naphilArray[i]
				sum += uint64(p)
				if p > maxLuma {
					maxLuma = p
				}
				i++
				if maxLuma == 255 {
					break
				}
			}
		}
	}
	if i < b {
		return (0xFF00 << 24) + sumNaphil(naphilArray, i, b)
	}
	return sum + (uint64(minLuma) << 24) + (uint64(maxLuma) << 32)
}

/*A recursive function involved in combining arrays*/
func combineArraysRec(fileNames []string, a int, b int, margin float64, tNum int) ([]Grid, []uint8, int) {
	if a < b {
		array1, naphil1, size1 := combineArraysRec(fileNames, a, a+((b-a)/2), margin, tNum)
		array2, naphil2, size2 := combineArraysRec(fileNames, a+((b-a)/2)+1, b, margin, tNum)
		if array1 == nil || size1 == 0 {
			return array2, naphil2, size2
		}
		if array2 == nil || size2 == 0 {
			return array1, naphil1, size1
		}
		return combineArrays(array1, array2, margin, tNum, naphil1, naphil2)
	}
	var array []Grid
	var naphil []uint8
	var err error
	var i_, arrayLen int
	var margInt uint8
	array, naphil, err = readFromFile(fileNames[a])
	if err != nil {
		panic("Invalid file")
	}
	i_ = 0
	arrayLen = len(array)
	margInt = uint8(256.0 * margin)
	/*Marks grids with a substantial difference between maximum
	and minimum value, then sorts.*/
	for i_ < arrayLen {
		if array[i_].maxLuma-array[i_].minLuma > margInt {
			array[i_].dimCornAvg |= 0x0F00000000000000
		}
		i_++
	}
	parallelSort(array, tNum)
	return array, naphil, len(array)
}

func main() {
	rand.Seed(time.Now().UnixNano())

	proFile, err := os.Create("Luma.prof")

	if err != nil {
		fmt.Println(err)
		return
	}

	pprof.StartCPUProfile(proFile)
	defer pprof.StopCPUProfile()

	/*The following options are as such:
	-i	Used to specify an input image or set of input images with a
		minimum and maximum grid size and a margin of error, in order
		to generate a set of grids
	-l	Used to specify an input file of a grid array, or more than
		one such file with a margin of error
	-y	Used to specify an input image on which to perform a luma
		trace
	-o	Used to specify exactly one output image
	-k	Used to specify exactly one output file for a grid array
	-t	Used to specify number of threads in certain processes, default 1
	*/
	kArray := make([]string, 0)
	iArray := make([]string, 0)
	lArray := make([]string, 0)
	yArray := make([]string, 0)
	oArray := make([]string, 0)
	tArray := make([]string, 0)
	array := make([]Grid, 0)
	arrayFromImg := make([]Grid, 0)
	arrayFromFile := make([]Grid, 0)
	var arrayLen int
	var arrayImgLen int
	var arrayFileLen int
	var naphilArray []uint8
	var imageDataNaphil []uint8
	var fileDataNaphil []uint8
	//var traceNaphil []uint8
	args := os.Args
	/*The following for loop creates arrays correspdonding to each of the
	above arguments.*/
	for i := 1; i < len(args); i++ {
		if args[i] == "-k" {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				kArray = append(kArray, args[j])
				j++
			}
			i = j - 1
		} else if args[i] == "-o" {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				oArray = append(oArray, args[j])
				j++
			}
			i = j - 1
		} else if args[i] == "-i" {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				iArray = append(iArray, args[j])
				j++
			}
			i = j - 1
		} else if args[i] == "-l" {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				lArray = append(lArray, args[j])
				j++
			}
			i = j - 1
		} else if args[i] == "-y" {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				yArray = append(yArray, args[j])
				j++
			}
			i = j - 1
		} else if args[i] == "-h" {
			fmt.Println("This is Luma. It is a program meant to accept input from an image to create a dataset, use this dataset to trace another image, and recreate that image with the texture of the images used for the dataset. It operates by breaking input images and trace images into fragments, discarding redundant fragments, and replacing fragments of a traced image with fragments from input images. The options for the Luma are as follows:")
			fmt.Println("	-i	Input one or more images to create a dataset, followed by minimum and maximum dimensions of fragments and the margin of redundancy. For example, 0.1 as a margin will discard a fragment if it is found to be at least 90% similar to another.")
			fmt.Println("e.g.	-i inputImage.png (inputImage2.png) 4 10 0.2")
			fmt.Println("	-l	Input one or more dataset that has already been generated by Luma. Multiple datasets must be followed by a margin of redundancy as well.")
			fmt.Println("e.g.	-l dataSet (dataSet2 0.1)")
			fmt.Println("	-y	Perform a tracing of an image or set of images, with minimum and maximum fragment dimensions.")
			fmt.Println("e.g	(-i or -l option) -y baseImage.png 4 10")
			fmt.Println("	-o	Output an image or set of images created by a trace.")
			fmt.Println("	-k	Save a dataset")
			fmt.Println("e.g.	(-i or -l option) -k newDataSet")
			fmt.Println("The original purpose of this program was to make digitally-created images appear hand-drawn. However, it can be used for texturing of any kind.")
			return
		} else if args[i] == "-t" {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				tArray = append(tArray, args[j])
				j++
			}
			i = j - 1
		}
	}
	/*These handle discoordinate arguments and arguments with an incorrect number of
	parameters.
	*/
	if len(kArray) == 0 && len(oArray) == 0 {
		if len(lArray) == 0 && len(iArray) == 0 && len(yArray) == 0 {
			fmt.Println("See list of options with -h.")
		} else {
			fmt.Println("Insufficient arguments, please specify either an output image using -o or an output dataset using -k")
		}
		return
	}
	if len(kArray) > 0 && len(iArray) == 0 && len(lArray) == 0 {
		fmt.Println("Output dataset specified without specifying input image using -i or input dataset using -l")
		return
	}
	if len(oArray) > 0 && (len(yArray) == 0 || (len(lArray) == 0 && len(iArray) == 0)) {
		fmt.Println("Output image specified without base image specified by -y or input image specified with -i or input dataset specified with -l")
		return
	}
	if len(oArray) > 1 {
		fmt.Printf("Please specify an output image file or a range with %c%c%cd, with X being the number of leading zeroes.\n", '%', '0', 'X')
		return
	}
	if len(yArray) > 0 && len(lArray) == 0 && len(iArray) == 0 {
		fmt.Println("Base image specified without input image specified with -i or input dataset specified with -l")
		return
	}
	if len(yArray) > 0 && len(oArray) == 0 {
		fmt.Println("Base image specified without output image specified with -o")
		return
	}
	if len(kArray) > 1 {
		fmt.Println("Too many dataset outputs specified. Please specify EXACTLY ONE output dataset.")
		return
	}
	if len(lArray) == 2 {
		fmt.Println("Invalid options for dataset inputs. Either specify exactly one input dataset or specify more than one dataset with a margin.")
		return
	}
	if len(iArray) > 0 && len(iArray) < 4 {
		fmt.Println("Please specify input image(s), minimum and maximum grid dimensions, and margin, in that exact order.")
		return
	}
	if len(iArray)-3 > 0x3FFFFF {
		fmt.Println("Too many images.")
		return
	}
	if len(yArray) > 0 && len(yArray) < 3 {
		fmt.Println("Please specify at least one base image file, minimum and maximum grid dimensions, in that exact order.")
		return
	}
	if len(tArray) > 1 {
		fmt.Println("Please specify one argument for thread number.")
		return
	}
	/*This handles inputting one or more file containing a grid array.*/
	tNum := 1
	if len(tArray) == 1 {
		t64, errT := strconv.ParseUint(tArray[0], 10, 8)
		tNum := t64
		if errT != nil {
			fmt.Println("Please specify an integer for thread number")
			log.Fatal(err)
			return
		}
		if tNum < 1 {
			fmt.Println("Please specify a positive integer for thread number")
			return
		}
		fmt.Printf("Thread num: %d\n", tNum)
	}

	if len(iArray) > 0 || len(lArray) > 0 {
		var errMarg error
		margin := float64(-1)
		/*Take grid data from images*/
		if len(iArray) > 0 {
			minIn, errMin := strconv.ParseUint(iArray[len(iArray)-3], 10, 8)
			maxIn, errMax := strconv.ParseUint(iArray[len(iArray)-2], 10, 8)
			minIn_64 := uint64(minIn)
			if maxIn < minIn*2 {
				fmt.Println("Please specify a maximum size at least twice that of the minimum size.")
				return
			}
			if maxIn > 255 || minIn > 255 {
				fmt.Println("Please specify maximum and minimum sizes BELOW 256")
			}
			margin, errMarg = strconv.ParseFloat(iArray[len(iArray)-1], 64)
			if nil != errMin || nil != errMax || nil != errMarg {
				fmt.Println("Please specify minimum and maximum grid dimensions and margin, in that order, AFTER all input images.")
				if nil != errMin {
					log.Fatal(errMin)
				} else if nil != errMax {
					log.Fatal(errMax)
				} else if nil != errMarg {
					log.Fatal(errMarg)
				}
				return
			}
			startTemp := time.Now().UnixNano()
			trees := make([]*Tree, len(iArray)-3)

			totalLeafNum := 0
			fmt.Printf("Generating trees:\n")
			startTime := time.Now().UnixNano()
			tempTime := time.Now().UnixNano()
			var wg sync.WaitGroup
			widthArray := make([]uint16, len(trees))
			heightArray := make([]uint16, len(trees))
			totalArea := 0
			/*Go image by image*/
			for jj := 0; jj < len(trees); jj += tNum {
				if time.Now().UnixNano()-tempTime > 1000000000 {
					fmt.Printf("%f\n", 100.0*float32(jj)/float32(len(trees)))
					tempTime = time.Now().UnixNano()
				}
				for kk := range tNum {
					wg.Add(1)
					go func(kk int) {
						defer wg.Done()
						i := jj + kk
						if i < len(trees) {
							f, err := os.Open(iArray[i])
							if err != nil {
								panic(err)
							}
							defer f.Close()
							config, _, err := image.DecodeConfig(f)
							if err != nil {
								panic(err)
							}
							w := config.Width
							h := config.Height
							if w > 8191 || h > 8191 {
								fmt.Println("Please choose images with dimensions below 8192.")
								return
							}
							widthArray[i] = uint16(w)
							heightArray[i] = uint16(h)
							totalArea += (w * h)
							/*Generate tree*/
							trees[i] = generateTree(0, uint64(w), 0, uint64(h), minIn_64, uint64(maxIn), rand.Uint64(), rand.Uint64())
							totalLeafNum += trees[i].leafNum
						}
					}(kk)
				}
				wg.Wait()
			}
			end := time.Now().UnixNano()
			timeTotal := (end - startTime)
			printTime(timeTotal)

			coordArray := make([][]uint64, totalLeafNum)
			indexArray := make([]int, totalLeafNum)
			encodedCoordArray := make([]uint64, totalLeafNum)
			tempLeafNum := 0

			fmt.Printf("Gathering coordinates from trees:\n")
			tempIndex := 0
			startTime = time.Now().UnixNano()
			tempTime = time.Now().UnixNano()
			/*The changeArray finds where the metadata array changes in terms of the dimensions
			or source image referred to. Its size will always be
			(((max-min+1)^2)*img_num)+1
			where img_num is the number of images.*/
			img_step := int(maxIn - minIn + 1)
			img_step *= img_step
			changeArraySize := img_step * len(trees)
			changeArraySize++
			changeArray := make([]int, changeArraySize)
			changeArray[changeArraySize-1] = totalLeafNum
			changeArraySize = 1
			/*Get the total number of leaves which will be the same as the total number of grids.*/
			for i := range trees {
				if time.Now().UnixNano()-tempTime > 1000000000 {
					fmt.Printf("%f\n", 100.0*float32(i)/float32(len(trees)))
					tempTime = time.Now().UnixNano()
				}
				reuse := make([]uint64, 5)
				coordsFromTree(trees[i], uint64(i), coordArray, tempLeafNum, reuse)
				/*Encode grid metadata into uint64 array*/
				encodeCoords(trees[i], uint64(i), encodedCoordArray, tempLeafNum)
				l := trees[i].leafNum
				tEnd := tempLeafNum + l
				/*Sort these grids based on width and height*/
				sort.Slice(encodedCoordArray[tempLeafNum:tEnd], func(i, j int) bool {
					return encodedCoordArray[tempLeafNum+i] < encodedCoordArray[tempLeafNum+j]
				})
				wh := uint64(0)
				w_ := 0
				h_ := 0
				/*Calculate the offsets for each grid in the naphil array*/
				for j := tempLeafNum; j < tEnd; j++ {
					indexArray[j] = tempIndex
					enc := encodedCoordArray[j]
					/*If a grid which will not have the same dimensions as
					the one previous is found, re-extract dimensions.*/
					if (enc>>26)&0xFFFF != wh {
						enc >>= 26
						wh = enc & 0xFFFF
						h_ = int(enc & 255)
						enc >>= 8
						w_ = int(enc & 255)
					}
					tempIndex += (w_ * h_)
				}
				tempLeafNum = tEnd
			}
			x1_ := 0
			changeArray[0] = 0
			var m int
			ignoreCoords := (^uint64(0x3FFFFFF))
			enc := encodedCoordArray[0]
			encOld := uint64(0xFFFFFFFFFFFFFFFF)
			imageEnd := trees[0].leafNum
			x2_ := imageEnd
			for x1_ < x2_ {
				m = x1_ + ((x2_ - x1_) / 2)
				if encodedCoordArray[m]&ignoreCoords != enc&ignoreCoords {
					x2_ = m
				} else {
					x1_ = m + 1
				}
			}
			for x1_ < totalLeafNum {
				/*Put the result of the bin search into changeArray*/
				changeArray[changeArraySize] = x1_
				/*Increment counter*/
				changeArraySize++
				/*Check if the next section of the grids metadata referss to a different
				source image*/
				encOld = enc >> 42
				if x1_ >= totalLeafNum {
					panic("Out of bounds")
				}
				enc = encodedCoordArray[x1_]
				if enc>>42 != encOld {
					imageEnd += trees[enc>>42].leafNum
				}
				/*Set the end of the next bin search to the last grid to be taken from the
				same source image*/
				x2_ = imageEnd
				/*Peform a binary search for the last grid with equal dimensions
				and from the same source image as the one at x1_*/
				for x1_ < x2_ {
					m = x1_ + ((x2_ - x1_) / 2)
					if encodedCoordArray[m]&ignoreCoords != enc&ignoreCoords {
						x2_ = m
					} else {
						x1_ = m + 1
					}
				}
			}
			/*Named after a race of mysterious beings mentioned in Genesis 6, later described of being
			great stature in Numbers 32 and usually translated as "giants" in other languages. This will
			indeed be a giant array.*/
			imageDataNaphil = make([]uint8, indexArray[totalLeafNum-1]+(int(maxIn)*int(maxIn)))
			end = time.Now().UnixNano()
			timeTotal = (end - startTemp)
			printTime(timeTotal)

			arrayFromImg = make([]Grid, totalLeafNum)
			tempLeafNum = 0
			fmt.Printf("Generating grids:\n")
			startTime = time.Now().UnixNano()
			tempTime = time.Now().UnixNano()

			margInt := uint8(margin * 256.0)

			for jj := 0; jj < len(trees); jj += int(tNum) {
				tln := 0
				for j := range jj {
					tln += trees[j].leafNum
				}
				if time.Now().UnixNano()-tempTime > 1000000000 {
					fmt.Printf("%f\n", 100.0*float32(jj)/float32(len(iArray)-3))
					tempTime = time.Now().UnixNano()
				}
				for kk := range int(tNum) {
					wg.Add(1)
					go func(kk int) {
						defer wg.Done()
						i := jj + kk
						i_64 := uint64(i)
						/*If cursor points to a valid image*/
						if i < len(trees) {
							/*Retrive the width of the image, store it as a signed value*/
							imgW_64 := uint64(widthArray[i])
							imgH_64 := uint64(heightArray[i])
							imgW_signed := int(imgW_64)
							/*Get a grayscale representation of the same image*/
							pix_data := func(iArray []string, i int) []uint8 {
								grayImg := gocv.IMRead(iArray[i], gocv.IMReadGrayScale)

								if grayImg.Empty() {
									panic("Error loading image")
								}
								defer grayImg.Close()

								return grayImg.ToBytes()
							}(iArray, i)
							/*Find the part of the change array which refer to this image, set a loop to
							these endpoints*/
							cng_start := i * img_step
							cng_end := cng_start + img_step
							for c_outer := cng_start; c_outer < cng_end; c_outer++ {
								/*Get the encoded metadata for the first grid in the segment, and ignore
								all bits besides those containing grid dimensions. Extract these dimensions
								and save the 16 bits containing all of them for when the dimCornAvg of
								individual grids is set.*/
								enc_start := (encodedCoordArray[changeArray[c_outer]] >> 26) & 0xFFFF
								h_64 := enc_start & 255
								h_signed := int(h_64)
								h_8 := uint8(h_64)
								w_64 := (enc_start >> 8) & 255
								w_signed := int(w_64)
								w_8 := uint8(w_64)
								/*Get the end of the loop for the current segment*/
								loop_end := changeArray[c_outer+1]
								area := w_64 * h_64
								area_signed := h_signed * w_signed
								var enc, x1, y1, y2, sum, avg, dimCornAvg, crnr_64, corners uint64
								var x1_signed, offset, offset_n, end_n, start_p, end_p /*, j, end*/ int
								var y_offset, y2_signed int
								var maxLuma, minLuma, crnr uint8
								for c_sub := changeArray[c_outer]; c_sub < loop_end; c_sub++ {
									/*Get the metadata for an individual grid*/
									enc = encodedCoordArray[c_sub]
									if (enc >> 42) != i_64 {
										panic("Wrong image")
									}
									if (enc>>26)&0xFFFF != enc_start {
										panic("Wrong dimensions")
									}
									/*Extract the coordinates from the metadata*/
									y1 = (^enc) & 8191
									enc >>= 13
									x1 = (^enc) & 8191
									y2 = y1 + h_64
									if y1 > imgH_64 || y2 > imgH_64 || x1 > imgW_64 || x1+w_64 > imgW_64 {
										panic("Wrong coordinates")
									}
									y2_signed = int(y2)
									x1_signed = int(x1)
									offset = indexArray[c_sub]
									/*The variables offset_n and end_n are endpoints of the naphil array. They increment by the grid's
									width.*/
									end_n = offset + w_signed
									offset_n = offset
									offset_end := offset + area_signed
									y_offset = int(y1)
									/*The variables start_p and end_p are endpoints of the array containing image data. They increment
									by the image's width.*/
									start_p = (int(y1) * imgW_signed) + x1_signed
									end_p = start_p + w_signed
									/*Copy data from the image into the naphil array*/
									for y_offset < y2_signed {
										copy(imageDataNaphil[offset_n:end_n], pix_data[start_p:end_p])
										offset_n += w_signed
										end_n += w_signed
										start_p += imgW_signed
										end_p += imgW_signed
										y_offset++
										if y_offset >= y2_signed {
											break
										}
										copy(imageDataNaphil[offset_n:end_n], pix_data[start_p:end_p])
										offset_n += w_signed
										end_n += w_signed
										start_p += imgW_signed
										end_p += imgW_signed
										y_offset++
										if y_offset >= y2_signed {
											break
										}
										copy(imageDataNaphil[offset_n:end_n], pix_data[start_p:end_p])
										offset_n += w_signed
										end_n += w_signed
										start_p += imgW_signed
										end_p += imgW_signed
										y_offset++
										if y_offset >= y2_signed {
											break
										}
										copy(imageDataNaphil[offset_n:end_n], pix_data[start_p:end_p])
										offset_n += w_signed
										end_n += w_signed
										start_p += imgW_signed
										end_p += imgW_signed
										y_offset++
									}

									/*Add the corners to the total sum, which will be used to calculate
									the average later*/
								minMaxLoopStart:
									crnr = imageDataNaphil[offset]
									maxLuma = crnr
									minLuma = crnr
									crnr_64 = uint64(crnr)
									corners = crnr_64
									sum = crnr_64
									corners <<= 8

									crnr = imageDataNaphil[offset+w_signed-1]
									if crnr > maxLuma {
										maxLuma = crnr
									} else if crnr < minLuma {
										minLuma = crnr
									}
									crnr_64 = uint64(crnr)
									corners += crnr_64
									sum += crnr_64
									corners <<= 8

									crnr = imageDataNaphil[offset_end-w_signed]
									if crnr > maxLuma {
										maxLuma = crnr
									} else if crnr < minLuma {
										minLuma = crnr
									}
									crnr_64 = uint64(crnr)
									corners += crnr_64
									sum += crnr_64
									corners <<= 8

									crnr = imageDataNaphil[offset_end-1]
									if crnr > maxLuma {
										maxLuma = crnr
									} else if crnr < minLuma {
										minLuma = crnr
									}
									crnr_64 = uint64(crnr)
									corners += crnr_64
									sum += crnr_64
									/*Check for the minimum and maximum values of all pixels except the corners,
									while adding them to the sum. A sweep is done for the top and bottom rows,
									and another for everything else.*/
									if minLuma != 0 || maxLuma != 255 {
										minMaxSum_result := minMaxSum(imageDataNaphil, offset+1, offset+w_signed-1, minLuma, maxLuma)
										sum += (minMaxSum_result & 0xFFFFFF)
										minMaxSum_result >>= 24
										minLuma = uint8(minMaxSum_result & 0xFF)
										minMaxSum_result >>= 8
										maxLuma = uint8(minMaxSum_result & 0xFF)
									} else {
										sum += sumNaphil(imageDataNaphil, offset+1, offset+w_signed-1)
									}
									if minLuma != 0 || maxLuma != 255 {
										minMaxSum_result := minMaxSum(imageDataNaphil, offset_end-w_signed+1, offset_end-1, minLuma, maxLuma)
										sum += (minMaxSum_result & 0xFFFFFF)
										minMaxSum_result >>= 24
										minLuma = uint8(minMaxSum_result & 0xFF)
										minMaxSum_result >>= 8
										maxLuma = uint8(minMaxSum_result & 0xFF)
									} else {
										sum += sumNaphil(imageDataNaphil, offset_end-w_signed+1, offset_end-1)
									}
									if minLuma != 0 || maxLuma != 255 {
										minMaxSum_result := minMaxSum(imageDataNaphil, offset+w_signed, offset_end-w_signed, minLuma, maxLuma)
										sum += (minMaxSum_result & 0xFFFFFF)
										minMaxSum_result >>= 24
										minLuma = uint8(minMaxSum_result & 0xFF)
										minMaxSum_result >>= 8
										maxLuma = uint8(minMaxSum_result & 0xFF)
									} else {
										sum += sumNaphil(imageDataNaphil, offset+w_signed, offset_end-w_signed)
									}

									/*Calculate the average*/
									avg = sum / area
									if avg > 255 {
										panic("Invalid average.")
									}
									if uint8(avg) < minLuma || uint8(avg) > maxLuma {
										goto minMaxLoopStart
									}

									/*The main purpose of dimCornAvg is for sorting. The intended algorithm is to sort all
									"shallow" grids (those with relatively low differences between min and max values) at
									the beginning, before all "deep" grids (those with relatively high differences). Then,
									the grids are to be sorted by width, height, average luma, and finally their corners.
									Since the actual difference between min and max is less important than the binary
									"deep-shallow" distinction, "deep" grids have some of the top bits set.
									The variable enc_start from earlier contains the width of the grid as its most signifcant
									eight bits and height as its least significant.*/
									dimCornAvg = uint64(0)
									if maxLuma-minLuma > margInt {
										dimCornAvg = 15
									}
									dimCornAvg <<= 16
									dimCornAvg += enc_start
									dimCornAvg <<= 8
									dimCornAvg += avg
									dimCornAvg <<= 32
									dimCornAvg += corners
									func() {
										arrayFromImg[c_sub] = Grid{
											w__:        w_8,
											h__:        h_8,
											minLuma:    minLuma,
											maxLuma:    maxLuma,
											avgLuma:    uint8(avg),
											dimCornAvg: dimCornAvg,
											offset:     offset,
										}
									}()
								}
							}
						}
					}(kk)
				}
				wg.Wait()
			}
			end = time.Now().UnixNano()
			timeTotal = (end - startTemp)
			printTime(timeTotal)

			arrayImgLen = len(arrayFromImg)

			fmt.Printf("Sorting started\n")
			parallelSort(arrayFromImg, tNum)
			fmt.Printf("Sorting completed\n")

			if margin > 0 {
				fmt.Println("Removing redundant grids")
				start = time.Now().UnixNano()
				startTemp = time.Now().UnixNano()
				arrayFromImg = removeRedundantGrids(arrayFromImg, margin, tNum, imageDataNaphil)
				end = time.Now().UnixNano()
				arrayImgLen = len(arrayFromImg)
				timeTotal := (end - startTemp)
				printTime(timeTotal)
			}
		}
		/*Take grid data from files previously created by Luma*/
		if len(lArray) > 0 {
			if len(lArray) == 1 {
				fmt.Println("Adding data from " + lArray[0])
				arrayFromFile, fileDataNaphil, err = readFromFile(lArray[0])
				if nil != err {
					fmt.Println("Please specify valid filenames for all input datasets.")
					log.Fatal(err)
					return
				}
				arrayFileLen = len(arrayFromFile)
				for i := range arrayFileLen {
					for arrayFromFile[i].getW() < 1 || arrayFromFile[i].getH() < 1 {
						arrayFromFile = slices.Delete(arrayFromFile, i, i+1)
						arrayFileLen--
					}
				}
				fmt.Printf("%v\n", len(arrayFromFile))
			}
			/*If there are multiple arguments for -l, a margin must go at the end, following
			VALID filenames.*/
			if len(lArray) > 2 {
				if margin < 0 {
					margin, err = strconv.ParseFloat(lArray[len(lArray)-1], 64)
					if nil != err {
						fmt.Println("Please specify margin AFTER all input datasets.")
						log.Fatal(err)
						return
					}
				}
				fmt.Println("Merging datasets...")
				arrayFromFile, fileDataNaphil, arrayFileLen = combineArraysRec(lArray, 0, len(lArray)-2, margin, tNum)
				fmt.Println("Datasets merged.")
			}
		}
		/*Combine data derived from both images and files*/
		if len(iArray) > 0 && len(lArray) > 0 {
			array, naphilArray, arrayLen = combineArrays(arrayFromImg, arrayFromFile, margin, tNum, imageDataNaphil, fileDataNaphil)
		} else if len(iArray) == 0 {
			array = arrayFromFile
			naphilArray = fileDataNaphil
			arrayLen = arrayFileLen
		} else {
			array = arrayFromImg
			naphilArray = imageDataNaphil
			arrayLen = arrayImgLen
		}
	}
	/*Trace an image*/
	if len(yArray) >= 3 {
		i_ := 0
		for i_ < arrayLen {
			g := array[i_]
			d := g.dimCornAvg
			d &= 0x00FFFFFF00000000
			maxL := g.maxLuma
			minL := g.minLuma
			d += (uint64(maxL-minL) << 24)
			d += (uint64(minL) << 16)
			d += (uint64(maxL) << 8)
			array[i_].dimCornAvg = d
			i_++
		}
		parallelSort(array, tNum)
		minIn, errMin := strconv.ParseUint(yArray[len(yArray)-2], 10, 8)
		maxIn, errMax := strconv.ParseUint(yArray[len(yArray)-1], 10, 8)
		if nil != errMin || nil != errMax {
			fmt.Println("Please specify minimum and maximum grid dimensions and margin, in that order, AFTER all input images.")
			if nil != errMin {
				log.Fatal(errMin)
			}
			if nil != errMax {
				log.Fatal(errMax)
			}
			return
		}
		if minIn > 255 || maxIn > 255 {
			fmt.Println("Please specify minimum and maximum values BELOW 256.")
			return
		}
		leadingZeroes := uint8(0)
		outputPrefix := ""
		outputSuffix := ""
		outputFileNames := make([]string, len(yArray)-2)
		commonImageFormats := [6]string{"PNG", "JPG", "JPEG", "BMP", "TIFF", "GIF"}
		cifLength := len(commonImageFormats)
		foundExt := int8(0)
		if len(yArray) == 3 {
			for i := range cifLength {
				if strings.HasSuffix(strings.ToUpper(oArray[i]), fmt.Sprintf("%s%s", ".", commonImageFormats[i])) {
					foundExt += 1
					break
				}
			}
			outputFileNames[0] = oArray[0]
			if foundExt == 0 {
				splitOnDot := strings.Split(yArray[0], ".")
				outputFileNames[0] = fmt.Sprintf("%s%s", outputFileNames[0], fmt.Sprintf("%s%s", ".", splitOnDot[len(splitOnDot)-1]))
			}
		} else {
			foundExt = int8(1)
			/*This searches for a replaceable digit string.*/
			r := regexp.MustCompile(`\%0[0-9][0-9]*d`)
			matches := r.FindAllString(oArray[0], -1)
			/*If there is no digit string, it looks fot the common file extensions
			in the name. If there is one, the program ends. Otherwise, it simply
			calculates how many digits there need to be.*/
			if nil == matches || len(matches) < 1 {
				foundExt = 0
				for i := range cifLength {
					if strings.HasSuffix(strings.ToUpper(oArray[0]), fmt.Sprintf("%s%s", ".", commonImageFormats[i])) {
						foundExt += 1
						break
					}
				}
				if foundExt != 0 {
					fmt.Printf("Please note, there is a file extension without a digit string. The extension will be subsumed into the file prefix. Digit strings are written '%c0Xd', where 'X' is the number of leading zeroes.\n", '%')
					foundExt = 1
				}
				outputPrefix = oArray[0]
				tenPow := 1
				for tenPow < (len(yArray)-2)/10 {
					tenPow *= 10
					leadingZeroes++
				}
			} else if len(matches) > 1 {
				fmt.Println("Please specify exactly one digit string.")
				return
			} else {
				prefEnd := strings.Index(oArray[0], matches[0])
				outputPrefix = oArray[0][:prefEnd]
				zz, err := strconv.ParseUint(string(matches[0][2:3]), 10, 8)
				if nil != err {
					fmt.Printf("Digit string not accepted: %s\n", matches[0])
					log.Fatal(err)
					return
				}
				leadingZeroes = uint8(zz)
				outputSuffix = oArray[0][prefEnd+len(matches[0]):]
				splitOnDot := strings.Split(outputSuffix, ".")
				if len(splitOnDot) != 1 {
					for i := 0; foundExt != 0 && i < cifLength; i++ {
						foundExt *= int8(strings.Compare(strings.ToUpper(splitOnDot[len(splitOnDot)-1]), commonImageFormats[i]))
					}
				}
			}
			/*The output filename does not include a (common) file extension.*/
			if foundExt != 0 {
				foundExt = int8((1 << cifLength) - 1)
				for i := range len(yArray) - 2 {
					for j := range cifLength {
						foundExt &= int8(^((1 - absInt(strings.Compare(strings.ToUpper(yArray[i][len(yArray[i])-len(commonImageFormats[j])-1:]), fmt.Sprint(".", commonImageFormats[j])))) << j))
					}
				}
				k := kern(uint8(foundExt))
				if k < cifLength {
					/*The input filenames collectively include one distinct (common) file extension.*/
					if cifLength-k == 1 {
						extCursor := int8(0)
						for 1&(foundExt>>extCursor) != 0 {
							extCursor++
						}
						outputSuffix += fmt.Sprintf("%s%s", ".", commonImageFormats[extCursor])
						/*The input filenames collectively include mutliple common extensions.*/
					} else if k < cifLength-1 {
						fmt.Println("Multiple extensions found among input files. Defaulting to PNG for output.")
						outputSuffix += ".png"
					}
					/*The input filenames do not collectively include any (common) file extensions.*/
				} else {
					fmt.Println("No valid extensions found among input files.")
					return
				}
			}
			for i := range len(yArray) - 2 {
				numStr := fmt.Sprintf("%d", i)
				for len(numStr) < int(leadingZeroes) {
					numStr = fmt.Sprintf("%s%s", "0", numStr)
				}
				outputFileNames[i] = fmt.Sprintf("%s%s%s", outputPrefix, numStr, outputSuffix)
			}
		}
		for i := range outputFileNames {
			for j := range len(yArray) - 2 {
				if strings.Compare(outputFileNames[i], yArray[j]) == 0 {
					fmt.Println("Setting output file name to input file name not permitted.")
					return
				}
			}
		}

		var wg sync.WaitGroup

		start = time.Now().UnixNano()
		for i := 0; i < len(yArray)-2; i += tNum {
			for j := range tNum {
				wg.Add(1)
				go func(i, j int) {
					defer wg.Done()
					if i+j < len(yArray)-2 {
						k := i + j
						img, err := openImage(yArray[k])
						if nil != err {
							fmt.Println("Please specify valid filenames for every input image.")
							log.Fatal(err)
							return
						}
						imgBnd := img.Bounds()
						w := imgBnd.Max.X
						h := imgBnd.Max.Y
						t := generateTree(0, uint64(w), 0, uint64(h), uint64(minIn), uint64(maxIn), rand.Uint64(), rand.Uint64())

						fmt.Println("Performing luma trace on " + yArray[k])
						grayImg := gocv.IMRead(yArray[k], gocv.IMReadGrayScale)

						if grayImg.Empty() {
							fmt.Println("Error loading image")
							os.Exit(1)
						}
						defer grayImg.Close()

						pix_data := grayImg.ToBytes()
						pix_data_out := lumaTrace(w, h, pix_data, array, arrayLen, t, naphilArray)

						matOut, err := gocv.NewMatFromBytes(h, w, gocv.MatTypeCV8U, pix_data_out)

						fmt.Println("Outputting to " + outputFileNames[k])
						gocv.IMWrite(outputFileNames[k], matOut)

					}
				}(i, j)
			}
			wg.Wait()
		}
		end := time.Now().UnixNano()
		printTime(end - start)
	}
	if len(kArray) == 1 {
		/*Sort based on range and max and then output*/
		if len(yArray) < 3 {
			i_ := 0
			for i_ < arrayLen {
				g := array[i_]
				d := g.dimCornAvg
				d &= 0x00FFFFFF00000000
				maxL := g.maxLuma
				d += (uint64(maxL-g.minLuma) << 24)
				d += (uint64(maxL) << 16)
				array[i_].dimCornAvg = d
				i_++
			}
		}
		parallelSort(array, tNum)
		fmt.Printf("Writing to file\n")
		writeToFile(array, arrayLen, kArray[0], naphilArray)
	}
}
