package main

import (
	"bufio"
	"fmt"
	"image"
	"image/color"
	"image/png"
	"log"
	"math"
	"math/rand"
	"os"
	"reflect"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

var start = time.Now().UnixNano()
var arraySize = 0
var wg sync.WaitGroup

/*Absolute difference between two unsigned 8-bit numbers.*/
func byteAbsDiff(a uint8, b uint8) uint8 {
	if a > b {
		return a - b
	}
	return b - a
}

/*
Max and min functions for two unsigned 32-bit integers,
used to correct errant shades of gray to solve a blotching
problem during colorization process.
*/
func maxUint32(a uint32, b uint32) uint32 {
	if a > b {
		return a
	}
	return b
}
func minUint32(a uint32, b uint32) uint32 {
	if a < b {
		return a
	}
	return b
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

/*Converts rgb values to grayscale*/
func grayscale(r_ uint8, g_ uint8, b_ uint8) uint8 {
	gr := 0.2126 * ((float64)(r_))
	gr += (0.7152 * ((float64)(g_)))
	gr += (0.0722 * ((float64)(b_)))
	return (uint8)(gr)
}

/*
A struct for a grid, containing a width, height, and an array of
gray pixels. It also keeps track of the highest, lowest, and
average value of these. It also once kept track of the median,
but the sorting involved was time-consuming and of limited
utility.
*/
type Grid struct {
	w       uint8
	h       uint8
	avgLuma uint8
	medLuma uint8
	maxLuma uint8
	minLuma uint8
	array   [][]uint8
	sum     uint8
}

/*
This sets the average values of a Grid, usually upon
instantiation.
*/
func (g *Grid) resetLuma() {
	//arrayCopy := make([]uint8, g.w*g.h)
	var sum uint32
	var i, j uint8
	g.maxLuma = 0
	g.minLuma = 255
	for i = 0; i < g.w; i++ {
		for j = 0; j < g.h; j++ {
			if g.array[i][j] > g.maxLuma {
				g.maxLuma = g.array[i][j]
			}
			if g.array[i][j] < g.minLuma {
				g.minLuma = g.array[i][j]
			}
			//arrayCopy[(i*g.h)+j] = g.array[i][j]
			sum += (uint32)(g.array[i][j])
		}
	}
	/*Here lie the remains of a process that calculated
	the median luma.*/
	//sort.Slice(arrayCopy, func(i, j int) bool { return arrayCopy[i] < arrayCopy[j] })
	//g.medLuma = (uint8)(arrayCopy[g.h*g.w/2])
	g.avgLuma = (uint8)(sum / ((uint32)(g.h) * (uint32)(g.w)))
}

/*
This returns whether one grid is "less than" another grid for the
purposes of sorting. Hierarchy is width, height, average brightness,
range of brightness levels, max brightness, and min brightness. There
is also an option to look for the first different corresponding
pixels between two grids if they otherwise would be sorted together.
This is not currently used, because this was one of the more substantial
bottlenecks of the program.
*/
func lessGrid(g1 Grid, g2 Grid, perPixel bool) bool {
	if g1.w < g2.w {
		return true
	}
	if g1.w > g2.w {
		return false
	}

	if g1.h < g2.h {
		return true
	}
	if g1.h > g2.h {
		return false
	}

	if g1.avgLuma < g2.avgLuma {
		return true
	}
	if g1.avgLuma > g2.avgLuma {
		return false
	}

	range1 := g1.maxLuma - g1.minLuma
	range2 := g2.maxLuma - g2.minLuma

	if range1 < range2 {
		return true
	}
	if range2 < range1 {
		return false
	}

	if g1.maxLuma < g2.maxLuma {
		return true
	}
	if g2.maxLuma < g1.maxLuma {
		return false
	}

	if g1.minLuma < g2.minLuma {
		return true
	}
	if g2.minLuma < g1.minLuma {
		return false
	}

	if perPixel {
		for i_ := uint8(0); i_ < g1.w; i_++ {
			for j_ := uint8(0); j_ < g1.h; j_++ {
				if g1.array[i_][j_] < g2.array[i_][j_] {
					return true
				}
				if g1.array[i_][j_] > g2.array[i_][j_] {
					return false
				}
			}
		}
	}
	return false
}

/*
This is a struct for a tree containing bounding x and y values, minimum
split values, children, and a two-bit variable to determine if it has
children. This is used to determine fragments of images to be turned into
grids.
*/
type Tree struct {
	x1          uint32
	x2          uint32
	y1          uint32
	y2          uint32
	minValid    uint8
	maxValid    uint8
	hasChildren uint8
	lTree       *Tree
	rTree       *Tree
	leafNum     int
}

/*This is a recursive instantiation method for a tree.*/
func generateTree(x1In uint32, x2In uint32, y1In uint32, y2In uint32, minIn uint8, maxIn uint8) *Tree {
	t := Tree{x1: x1In, x2: x2In, y1: y1In, y2: y2In, maxValid: maxIn, minValid: minIn, hasChildren: 0}
	if t.x2-t.x1 > uint32(maxIn) && (t.y2-t.y1 <= uint32(maxIn) || rand.Uint32()%2 != 1) {
		/*low := t.x2-t.x1
		high := 0*/
		mid := (t.x1 + uint32(t.minValid)) + (rand.Uint32() % (t.x2 - t.x1 - uint32(t.minValid)))
		for mid-t.x1 < uint32(t.minValid) || t.x2-mid < uint32(t.minValid) {
			mid = (t.x1 + uint32(t.minValid)) + (rand.Uint32() % (t.x2 - t.x1 - uint32(t.minValid)))
		}
		t.hasChildren = 3
		t.lTree = generateTree(t.x1, mid, t.y1, t.y2, t.minValid, t.maxValid)
		t.rTree = generateTree(mid, t.x2, t.y1, t.y2, t.minValid, t.maxValid)
		t.leafNum = t.lTree.leafNum + t.rTree.leafNum
	} else if t.y2-t.y1 > uint32(maxIn) {
		mid := (t.y1 + uint32(t.minValid)) + (rand.Uint32() % (t.y2 - t.y1 - uint32(t.minValid)))
		for mid-t.y1 < uint32(t.minValid) || t.y2-mid < uint32(t.minValid) {
			mid = (t.y1 + uint32(t.minValid)) + (rand.Uint32() % (t.y2 - t.y1 - uint32(t.minValid)))
		}
		t.hasChildren = 3
		t.lTree = generateTree(t.x1, t.x2, t.y1, mid, t.minValid, t.maxValid)
		t.rTree = generateTree(t.x1, t.x2, mid, t.y2, t.minValid, t.maxValid)
		t.leafNum = t.lTree.leafNum + t.rTree.leafNum
	} else {
		t.leafNum = 1
	}
	return &t
}

/*
This compares each pixel of two grids, stores their absolute difference, and returns the
sum.
*/
func gridDiff(g1 Grid, g2 Grid) uint32 {
	if g1.w != g2.w || g1.h != g2.h {
		return math.MaxUint32
	}
	sum := uint32(0)
	for i := uint8(0); i < g1.w; i++ {
		for j := uint8(0); j < g1.h; j++ {
			sum += uint32(byteAbsDiff(g1.array[i][j], g2.array[i][j]))
		}
	}
	return sum
}

/*
This determines if any two corresponding pixels have an absolute difference greater
than an arbitrarily-define value.
*/
func gridDiffMax(g1 Grid, g2 Grid, maxIn uint8) uint8 {
	if g1.w != g2.w || g1.h != g2.h {
		return 255
	}
	maxDiff := uint8(0)
	h := uint32(g1.h)
	w := uint32(g1.w)
	var c1, c2, flr, clg uint8
	if g2.maxLuma < maxIn {
		flr = 0
	} else {
		flr = g2.maxLuma - maxIn
	}
	if g2.maxLuma > 255-maxIn {
		clg = 255
	} else {
		clg = g2.maxLuma + maxIn
	}
	/*If one of the pixels from g1 is below the floor or above the
	ceiling, it has the potential to be different enough from the
	corresponding pixel in g2 to satisfy the question this function
	asks.*/
	for i := uint32(0); i < w; i++ {
		for j := uint32(0); j < h; j++ {
			c1 = g1.array[i][j]
			if c1 > clg {
				c2 = g2.array[i][j]
				if c2 < c1 && c1-c2 > maxIn {
					return c1 - c2
				}
			}
			if flr > c1 {
				c2 = g2.array[i][j]
				if c2 > c1 && c2-c1 > maxIn {
					return c2 - c1
				}
			}
		}
	}
	return maxDiff
}

/*
This finds the total difference between two grids, but will return early
under certain conditions.
*/
func gridDiffAlt(g1 Grid, g2 Grid, maxDiff uint8, crossRange uint8) uint32 {
	if g1.w != g2.w || g1.h != g2.h {
		return math.MaxUint32
	}
	/*Obviously, if the lowest of one grid is maxDiff above the maximum of the other grid,
	then all corresponding pixels have a difference greater than or equal to maxDiff.*/
	if (g2.maxLuma < 255-maxDiff && g1.minLuma > g2.maxLuma+maxDiff) || (g1.maxLuma < 255-maxDiff && g2.minLuma > g1.maxLuma+maxDiff) {
		return math.MaxUint32
	}
	sum := uint32(0)
	h32 := uint32(g1.h)
	area := uint32(g1.w) * h32
	maxSum := uint32(maxDiff) * uint32(g1.w) * uint32(g1.h)
	var pixel1, pixel2 uint8
	i := uint32(0)
	cr32 := uint32(crossRange)
	/*The third condition determines if there is still a mathematic possibility for the
	sum to exceed the maximum designated sum. Maintaining this loop to the end indeed
	is a tightrope balance, but adding this third condition solved a slowdown issue.*/
	for i < area && sum < maxSum && sum+((area-i)*cr32) > maxSum {
		pixel1 = g1.array[i/h32][i%h32]
		pixel2 = g2.array[i/h32][i%h32]
		sum += uint32(byteAbsDiff(pixel1, pixel2))
		i++
	}
	if i < area && sum < maxSum {
		return sum + ((area - i) * cr32)
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
This determines whether any corresponding corner pixels between two
grids have corners exceeded a margin. This solved a blotching problem.
*/
func maxCornerDiff(g1 Grid, g2 Grid, maxIn uint8) uint8 {
	if g1.w != g2.w || g1.h != g2.h {
		return 255
	}
	ww := int(g1.w - 1)
	hh := int(g1.h - 1)
	c1 := g1.array[0][0]
	c2 := g2.array[0][0]
	diffTemp := byteAbsDiff(c1, c2)
	if diffTemp < maxIn {
		c1 = g1.array[0][hh]
		c2 = g2.array[0][hh]
		diffTemp = byteAbsDiff(c1, c2)
		if diffTemp < maxIn {
			c1 = g1.array[ww][0]
			c2 = g2.array[ww][0]
			diffTemp = byteAbsDiff(c1, c2)
			if diffTemp < maxIn {
				c1 = g1.array[ww][hh]
				c2 = g2.array[ww][hh]
				return byteAbsDiff(c1, c2)
			}
		}
	}
	return diffTemp
}

/*
The returns the maximum possible difference between two grids,
not necessarily at the same position.
*/
func getCrossRange(g1 Grid, g2 Grid) uint8 {
	if g1.w != g2.w || g1.h != g2.h {
		return 255
	}
	crossRangeA := g1.maxLuma - g2.minLuma
	crossRangeB := g2.maxLuma - g1.minLuma
	if g1.maxLuma < g2.minLuma || crossRangeB > crossRangeA {
		return crossRangeB
	}
	return crossRangeA

}

/*
This compares an octet of grids against each other. Octets are explained in
removeRedundantGrids.
*/
func compareGridBoolSingle(array []Grid, margin float64, cursor uint32, octet uint8, u uint32, v uint32) uint8 {
	/*If there is only one remaining grid in the octet, return it unchanged.*/
	if u > 6 || v <= u || v-u < 2 {
		return octet
	}

	/*Get the subset of the octet that needs to be compared and, if it only has
	one remaining grid, return the octet unchanged.*/
	subset := octet
	if v < 8 {
		subset %= uint8(1 << v)
	}
	subset &= uint8(^((1 << u) - 1))
	if kern(subset) < 2 {
		return subset
	}

	/*The cursors in the grid array, which will be repeatedly referenced below.*/
	uc := (cursor << 3) + u
	vc := (cursor << 3) + v

	/*If there are exactly two grids remaining in the octet, and they are not
	comparable for reasons of different dimensions or different average brightness
	levels, simply return the octet unchanged.*/
	if vc-uc == 2 && (array[vc-1].h != array[uc].h || array[vc-1].w != array[uc].w || array[vc-1].avgLuma-array[uc].avgLuma >= uint8(256.0*margin)) {
		return subset
	}

	/*If the two grids at the ends have different dimensions, find the first grid
	with different dimensions than the first and subdivide.*/
	if array[uc].h != array[vc-1].h || array[uc].w != array[vc-1].w {
		uNew := u + 1
		for v < uNew && array[uc].h == array[(cursor<<3)|uNew].h && array[uc].w == array[(cursor<<3)|uNew].w {
			uNew++
		}
		octet1 := compareGridBoolSingle(array, margin, cursor, octet, u, uNew)
		octet2 := compareGridBoolSingle(array, margin, cursor, octet, uNew, v)
		return octet1 | octet2
	}

	/*If the two grids at the end have substantially different average brightness
	values*/
	margInt := uint8(margin * 256.0)
	if array[vc-1].avgLuma-array[uc].avgLuma >= margInt {
		/*If the average brightness levels of the two grids at the ends are within
		twice the specified margin, find the first with a brightness level substantially
		different than the first, and subdivide.*/
		if margInt < 128 && array[vc-1].avgLuma-array[uc].avgLuma <= margInt<<1 {
			uNew := u + 1
			for uNew < v && array[(cursor<<3)+uNew].avgLuma-array[uc].avgLuma < margInt {
				uNew++
			}
			octet1 := compareGridBoolSingle(array, margin, cursor, octet, u, uNew)
			octet2 := compareGridBoolSingle(array, margin, cursor, octet, uNew, v)
			return octet1 | octet2
		}
		/*If they are more than twice the margin, find the first grid that is "out of reach"
		of the two ends, and subdivide.*/
		uNew := u + 1
		vNew := v - 2
		for uNew < vNew {
			if array[(cursor<<3)|uNew].avgLuma-array[uc].avgLuma < margInt {
				uNew++
			} else if array[vc-1].avgLuma-array[(cursor<<3)+vNew].avgLuma < margInt {
				vNew--
				/*If the grids out of reach of the ends do not overlap, compare the subset of the
				octet within reach of the first, within reach of the last, and the gap they leave.*/
			} else {
				octet1 := compareGridBoolSingle(array, margin, cursor, octet, u, uNew)
				octet2 := compareGridBoolSingle(array, margin, cursor, octet, uNew, vNew)
				octet3 := compareGridBoolSingle(array, margin, cursor, octet, vNew, v)
				return octet1 | octet2 | octet3
			}
		}
		/*If the grids out of reach of the ends do overlap, just subdivide into two.*/
		octet1 := compareGridBoolSingle(array, margin, cursor, octet, u, uNew)
		octet2 := compareGridBoolSingle(array, margin, cursor, octet, uNew, v)
		return octet1 | octet2
	}
	/*Note, the above scenario should not be a common occurrence, particularly compared to that
	where grids of different dimensions are in the same octet, as changes in brightness are more
	gradual than changes in height or width in a sorted array.*/

	/*The endgame: the octet contains at least two set bits referring to grids which all have the
	same dimensions and similar brightness levels.*/
	area := uint32(array[uc].w) * uint32(array[uc].h)
	for w1 := u; w1 < v-1; w1++ {
		if (octet>>uint8(w1))%2 == 1 {
			/*If there is a grid remaining at w1*/
			a1 := array[(cursor<<3)+w1]
			range1 := a1.maxLuma - a1.minLuma
			w1_8 := uint8(w1)
			/*The grid at w1 might be eliminated, hence the first condition.*/
			for w2 := w1 + 1; (octet>>w1_8)%2 == 1 && w2 < v; w2++ {
				/*If there is a grid remaining at w2*/
				if (octet>>uint8(w2))%2 == 1 {
					a2 := array[(cursor<<3)+w2]
					range2 := a2.maxLuma - a2.minLuma
					/*If two grids have imilar ranges, compare*/
					if (range1 < margInt && range2 < margInt) || (range1 >= margInt && range2 >= margInt) {
						/*This gets the maximum possible difference between any two pixels between the
						grids, regardless of position. If it is within the margin, then one can be eliminated.*/
						crossRange := getCrossRange(a1, a2)
						/*Otherwise, if none of the corners of the girds differ outside the margin, there are
						two justifications for elimination: if the ranges are small and the overall difference
						is small; or if the ranges are large, while the largest difference between any
						corresponding pixels is still small.*/
						if crossRange < margInt || (maxCornerDiff(a1, a2, margInt) < margInt && ((range1 < margInt && gridDiffAlt(a1, a2, margInt, crossRange) < uint32(margInt)*area) || (range1 >= margInt && gridDiffMax(a1, a2, margInt) < margInt))) {
							if rand.Uint32()%2 == 0 {
								octet &= (^(1 << uint8(w1)))
							} else {
								octet &= (^(1 << uint8(w2)))
							}
						}
					}
				}
			}
		}
	}
	return octet
}

/*
This compares grids across two octets.
*/
func compareGridBool(array []Grid, margin float64, cursor1 uint32, cursor2 uint32, bool1 uint8, bool2 uint8, u1 uint32, v1 uint32, u2 uint32, v2 uint32) uint16 {
	margChar := uint8(margin * 256.0)
	v1_char := uint8(v1)
	v2_char := uint8(v2)
	u2_char := uint8(u2)
	i := uint8(u1)
	var a1 Grid
	var crossRange, corner1, corner2, corner3, corner4, cornerA, cornerB, range1 uint8
	j := u2_char
	u1 += 255

	/*The outer loop iterates through the first octet, and can be cut short if
	at least one of the two octets is completely eliminated*/
	for i < v1_char && bool1 != 0 && bool2 != 0 {
		/*If there is a remaining grid at i*/
		if (bool1>>i)%2 != 0 {
			/*Since u1 was never going to exceed 7 nor used otherwise in this
			loop, 255 is added to it when incrementing. This triggers the
			routine below to reset various values to be compared below, which
			resets u1 to its original value. This is because i might not
			necessarily be incremented during a cycle of this loop, and this
			prevents repeated reevaluations from grids which might have
			already been eliminated..*/
			if u1 > 255 {
				u1 %= 255
				a1 = array[(cursor1<<3)+uint32(i)]
				range1 = a1.maxLuma - a1.minLuma
				/*Calculating corners here provides a slight speed boost compared
				to using maxCornerDiff.*/
				corner1 = a1.array[0][0]
				corner2 = a1.array[0][a1.h-1]
				corner3 = a1.array[a1.w-1][0]
				corner4 = a1.array[a1.w-1][a1.h-1]
				cornerA = corner1
				if corner2 < cornerA {
					cornerA = corner2
				}
				if corner3 < cornerA {
					cornerA = corner3
				}
				if corner4 < cornerA {
					cornerA = corner4
				}
				cornerB = corner1
				if corner2 > cornerB {
					cornerB = corner2
				}
				if corner3 > cornerB {
					cornerB = corner3
				}
				if corner4 > cornerB {
					cornerB = corner4
				}
				j = u2_char
			}
			if j < v2_char {
				/*If there is a remaining grid at j*/
				if (bool2>>j)%2 != 0 {
					a2 := array[(cursor2<<3)+uint32(j)]
					range2 := a2.maxLuma - a2.minLuma
					/*Since comparison takes place across grids, there is still the
					possibiility that two grids might have different dimensions or
					substantially different average brightness levels, and
					particularly different ranges.*/
					if a2.h == a1.h && a2.w == a1.w && a2.avgLuma-a1.avgLuma < margChar && ((range1 < margChar && range2 < margChar) || (range1 >= margChar && range2 >= margChar)) {
						crossRange = getCrossRange(a1, a2)
						/*Same rules apply as in compareGridBoolSingle to determine
						whether either should be eliminated.*/
						if crossRange < margChar || ((cornerB > 255-margChar || a2.minLuma < cornerB+margChar) &&
							(cornerA < margChar || a2.maxLuma > cornerA-margChar) &&
							byteAbsDiff(corner1, a2.array[0][0]) < margChar &&
							byteAbsDiff(corner2, a2.array[0][a1.h-1]) < margChar &&
							byteAbsDiff(corner3, a2.array[a1.w-1][0]) < margChar &&
							byteAbsDiff(corner4, a2.array[a1.w-1][a1.h-1]) < margChar &&
							((range1 < margChar && gridDiffAlt(a1, a2, margChar, crossRange) < uint32(margChar)*uint32(a1.w)*uint32(a1.h)) || (range1 >= margChar && gridDiffMax(a1, a2, margChar) < margChar))) {
							if rand.Uint32()%2 != 0 {
								bool1 &= (^(1 << uint8(i)))
							} else {
								bool2 &= (^(1 << uint8(j)))
							}
						}
					}
				}
			}
			if bool2>>j != 0 && (bool1>>i)%2 != 0 {
				j++
			} else {
				j = 255
			}
		}
		if bool1>>i != 0 {
			i++
			u1 += 255
		} else {
			i = 255
		}
	}
	/*Return both octets back as 16-bit value.*/
	return uint16(bool1) + (uint16(bool2) << 8)
}

/*Location of the first set bit*/
func firstSet(octet uint8) uint8 {
	u := uint8(0)
	for u < 8 {
		if (octet>>u)%2 == 1 {
			return u
		}
		u++
	}
	return 8
}

/*Location of the last set bit*/
func lastSet(octet uint8, u uint8) uint8 {
	v := u
	for v < 8 && octet>>v != 0 {
		v++
	}
	return v
}

/*This is the intermediary between removeRedundantGrids and compareGridBool.*/
func compareDoubles(boolArray []uint8, a uint32, b uint32, array []Grid, u1 uint32, v1 uint32, margin float64, tNum uint32) {
	margChar := uint8(margin * 256.0)
	gv := array[(a<<3)+(v1-1)]
	remOct := b - (a + 1)
	modT := uint32(0)
	tNumAct := tNum
	octPer := uint32(1)
	if remOct > tNum {
		modT = remOct % tNum
		octPer = remOct / tNum
	} else if remOct < tNum {
		tNumAct = remOct
	}
	wg.Add(int(tNumAct))
	for t := uint32(0); boolArray[a] != 0 && t < tNumAct; t++ {
		go func(t uint32) {
			defer wg.Done()
			for k := uint32(0); boolArray[a] != 0 && k < octPer; k++ {
				if boolArray[(t*octPer)+k+a+1] != 0 {
					ii := (t * octPer) + k + a + 1
					u2 := uint32(firstSet(boolArray[ii]))
					for u2 > 0 && (ii<<3)+u2 >= uint32(len(array)) {
						u2--
					}
					for u2 > 0 && (boolArray[ii]>>uint8(u1))%2 == 0 {
						u2--
					}
					if array[(ii<<3)+u2].h == gv.h && array[(ii<<3)+u2].w == gv.w && array[(ii<<3)+u2].avgLuma-gv.avgLuma < margChar {
						v2 := u2 + 1
						for v2 < 8 && boolArray[ii]>>uint8(v2) == 1 && array[(ii<<3)+v2].h == gv.h && array[(ii<<3)+v2].w == gv.w {
							v2++
						}
						doublet := compareGridBool(array, margin, a, ii, boolArray[a], boolArray[ii], u1, v2, u2, v2)
						newA := uint8(doublet % 256)
						/*If the first octet has changed, make the necessary adjustments*/
						if newA != boolArray[a] {
							if newA != 0 {
								u1 := uint32(firstSet(newA))
								for u1 > 0 && (a<<3)+u1 >= uint32(len(array)) {
									u1--
								}
								for u1 > 0 && (newA>>uint8(u1))%2 == 0 {
									u1--
								}
								v1 = uint32(lastSet(newA, uint8(u1)+1))
								for v1 > u1 && (a<<3)+(v1-1) >= uint32(len(array)) {
									v1--
								}
								for v1 > u1 && (newA>>uint8(v1-1))%2 == 0 {
									v1--
								}
								gv = array[(a<<3)+(v1-1)]
							}
							boolArray[a] = newA
						}
						boolArray[ii] = uint8(doublet >> 8)
					}
				}
			}
		}(t)
	}
	wg.Wait()
	if modT > 0 && boolArray[a] != 0 {
		wg.Add(int(modT))
		for t := b - modT; boolArray[a] != 0 && t < b; t++ {
			go func(t uint32) {
				defer wg.Done()
				if t < uint32(len(boolArray)) && boolArray[t] != 0 {
					u2 := uint32(firstSet(boolArray[t]))
					for u2 > 0 && (t<<3)+u2 >= uint32(len(array)) {
						u2--
					}
					for u2 > 0 && (boolArray[t]>>uint8(u1))%2 == 0 {
						u2--
					}
					if array[(t<<3)|u2].h == gv.h && array[(t<<3)|u2].w == gv.w && array[(t<<3)|u2].avgLuma-gv.avgLuma < margChar {
						v2 := u2 + 1
						for v2 < 8 && (boolArray[t]>>uint8(v2))%2 == 1 && array[(t<<3)|u2].h == gv.h && array[(t<<3)|u2].w == gv.w && array[(t<<3)|u2].avgLuma-gv.avgLuma < margChar {
							v2++
						}
						doublet := compareGridBool(array, margin, a, t, boolArray[a], boolArray[t], u1, v2, u2, v2)
						newA := uint8(doublet % 256)
						/*If the first octet has changed, make the necessary adjustments*/
						if newA != boolArray[a] {
							if newA != 0 {
								u1 := uint32(firstSet(newA))
								for u1 > 0 && (a<<3)+u1 >= uint32(len(array)) {
									u1--
								}
								for u1 > 0 && (newA>>uint8(u1))%2 == 0 {
									u1--
								}
								v1 = uint32(lastSet(newA, uint8(u1)+1))
								for v1 > u1 && (a<<3)+(v1-1) >= uint32(len(array)) {
									v1--
								}
								for v1 > u1 && (newA>>uint8(v1-1))%2 == 0 {
									v1--
								}
								gv = array[(a<<3)+(v1-1)]
							}
							boolArray[a] = newA
						}
						boolArray[t] = uint8(doublet >> 8)
					}
				}
			}(t)
		}
		wg.Wait()
	}
	/*for i := a + 1; boolArray[a] != 0 && i < b; i++ {
		if boolArray[i] != 0 {
			u2 := uint32(firstSet(boolArray[i]))
			for u2 > 0 && (i<<3)+u2 >= uint32(len(array)) {
				u2--
			}
			for u2 > 0 && (boolArray[i]>>uint8(u1))%2 == 0 {
				u2--
			}
			if array[(i<<3)+u2].h == gv.h && array[(i<<3)+u2].w == gv.w && array[(i<<3)+u2].avgLuma-gv.avgLuma < margChar {
				v2 := u2 + 1
				for v2 < 8 && boolArray[i]>>uint8(v2) == 1 && array[(i<<3)+v2].h == gv.h && array[(i<<3)+v2].w == gv.w {
					v2++
				}
				if compCond == 1 ||
					(compCond == 0 && array[(i<<3)+u2].maxLuma-array[(i<<3)+u2].minLuma < margChar) ||
					(compCond == 2 && array[(i<<3)+u2].maxLuma-array[(i<<3)+u2].minLuma > margChar) {
					doublet := compareGridBool(array, margin, a, i, boolArray[a], boolArray[i], u1, v2, u2, v2)
					newA := uint8(doublet % 256)
					if newA != boolArray[a] {
						if newA != 0 {
							u1 := uint32(firstSet(newA))
							for u1 > 0 && (a<<3)+u1 >= uint32(len(array)) {
								u1--
							}
							for u1 > 0 && (newA>>uint8(u1))%2 == 0 {
								u1--
							}
							v1 = uint32(lastSet(newA, uint8(u1)+1))
							for v1 > u1 && (a<<3)+(v1-1) >= uint32(len(array)) {
								v1--
							}
							for v1 > u1 && (newA>>uint8(v1-1))%2 == 0 {
								v1--
							}
							gv = array[(a<<3)+(v1-1)]
							if array[(a<<3)+u1].maxLuma-array[(a<<3)+u1].minLuma > margChar {
								compCond = 2
							}
							if array[(a<<3)+(v1-1)].maxLuma-array[(a<<3)+(v1-1)].minLuma > margChar {
								compCond = 1
							}
						}
						boolArray[a] = newA
					}
					boolArray[i] = uint8(doublet >> 8)
				}
			}
		}
	}*/
}

/*
This finds the closest cursor in an array to a grid with the
specified width, height, and average luma value, using a binary
search.
*/
func mostComparableCursor(array []Grid, a uint32, b uint32, targetW uint8, targetH uint8, targetLuma uint8) uint32 {
	var m uint32
	for a < b {
		m = a + ((b - a) >> 1)
		if array[m].w > targetW || (array[m].w == targetW && (array[m].h > targetH || (array[m].h == targetH && array[m].avgLuma >= targetLuma))) {
			b = m
		} else {
			a = m + 1
		}
	}
	return a
}

/*
This determines whether two grids are identical. It is
used when restructuring a pruned array.
*/
func isDupe(g1 Grid, g2 Grid) bool {
	if g1.w != g2.w {
		return false
	}
	if g1.h != g2.h {
		return false
	}
	if g1.avgLuma != g2.avgLuma {
		return false
	}
	if g1.maxLuma != g2.maxLuma {
		return false
	}
	if g1.minLuma != g2.minLuma {
		return false
	}
	w32 := uint32(g1.w)
	h32 := uint32(g1.h)
	for i := uint32(0); i < w32; i++ {
		for j := uint32(0); j < h32; j++ {
			if g1.array[i][j] != g2.array[i][j] {
				return false
			}
		}
	}
	return true
}

/*
After redundant grids have been found, this places all of them
at the end, and the non-redundant grids at the beginning.
Grids are set to 0 dimensions instead of being deleted from the
slice to reduce garbage collection time.
*/
func restructuredBoolArray(boolArray []uint8, boolLen uint32, array []Grid, arrayLen uint32) {
	newTotal := uint32(0)
	for i := uint32(0); i < boolLen; i++ {
		newTotal += uint32(kern(boolArray[i]))
	}

	if newTotal >= arrayLen {
		return
	}
	/*This indicates how many swaps there have been between redundant
	and non-redundant grids.*/
	resettled := uint32(0)

	/*This value, ii, is the cursor meant to seek out eliminated grids.*/
	ii := uint32(0)
	for ii < arrayLen && (boolArray[ii>>3]>>uint8(ii%8))%2 == 1 {
		ii++
	}
	/*This value, jj, is meant to seek out grids that have not been
	eliminated.*/
	jj := ii + 1
	for jj < arrayLen && jj>>3 < boolLen && (boolArray[jj>>3]>>uint8(jj%8))%2 == 0 {
		jj++
	}

	/*T*/
	for jj < arrayLen && jj>>3 < boolLen && resettled < newTotal {
		/*If jj is not at a non-redundant grid, continue seeking one out. */
		if (boolArray[jj>>3]>>uint8(jj%8))%2 == 0 {
			jj++
			/*If it is, and ii is at a redundant grid, swap them.*/
		} else if (boolArray[ii>>3]>>uint8(ii%8))%2 == 0 {
			if !isDupe(array[ii], array[jj]) {
				array[ii], array[jj] = array[jj], array[ii]
			}
			array[jj].w = 0
			array[jj].h = 0
			resettled++
			boolArray[ii>>3] |= (1 << (ii % 8))
			boolArray[jj>>3] &= (^(1 << (jj % 8)))
			ii++
			jj++
			/*If ii is not at a redundant grid, continue seeking one out.*/
		} else {
			ii++
		}
	}
	ii = resettled
	/*Clear out the remaining grids.*/
	for ii < arrayLen {
		if array[ii].w != 0 || array[ii].h != 0 {
			array[ii].w = 0
			array[ii].h = 0
		}
		ii++
	}
}

/*This eliminates grids that are similar within a margin.*/
func removeRedundantGrids(array []Grid, margin float64, tNum uint32) []Grid {
	singleTime := int64(0)
	doubleTime := int64(0)
	arrayLen := uint32(len(array))
	margInt := uint8(margin * 256.0)

	/*The set of grids which will remain is expressed in an array of
	8-bit integers, each called an octet. If they are set at the end
	of this process, that means they stay. If they are unsset, that
	means they go.
	The extra statements in the length of the octet array is to
	accomodate numbers of grids that are not divisible by 8.*/
	boolLen := (arrayLen >> 3) + ((arrayLen % 2) | ((arrayLen >> 1) % 2) | ((arrayLen >> 2) % 2))
	boolArray := make([]uint8, boolLen)
	for i := uint32(0); i < boolLen; i++ {
		boolArray[i] = 255
	}
	if arrayLen%8 != 0 {
		boolArray[boolLen-1] = uint8((1 << (arrayLen % 8)) - 1)
	}

	/*Every byte is internally compared, and bits are unset if they
	correspond to a grid that is too similar to a previous grid.
	Afterwards, each remaining grid described by the bit is compared
	to all subsequent grids of the same dimensions and similar
	average brightness level, unsetting bits if necessary. This ensures
	no pair of grids is compared twice.*/
	for i := uint32(0); i < boolLen; i++ {
		/*Tell the user how much of the array has been examined.*/
		if 1000000000 < time.Now().UnixNano()-start {
			fmt.Printf("%f%%\n", 100.0*float64(i)/float64(arrayLen>>3))
			start = time.Now().UnixNano()
		}

		/*If an octet still has at least two remaining grids*/
		if boolArray[i] != 0 && kern(boolArray[i]) > 1 {

			/*Find its first grid, and dial it back if, for
			whatever reason, the initial search went out of
			bounds.*/
			u := uint32(firstSet(boolArray[i]))
			for u > 0 && (i<<3)+u >= arrayLen {
				u--
			}
			for u > 0 && (boolArray[i]>>u)%2 == 0 {
				u--
			}

			/*If the search did not go out of bounds*/
			if (boolArray[i]>>u)%2 == 1 {
				/*Find the cursor after the last set bit, and adjust
				if it went out of bounds.*/
				v := uint32(lastSet(boolArray[i], uint8(u+1)))
				for v > 1 && (i<<3)+(v-1) >= arrayLen {
					v--
				}
				for v > 1 && (boolArray[i]>>(v-1))%2 == 0 {
					v--
				}

				/*If the above search did not go out of bounds*/
				if (boolArray[i]>>(v-1))%2 == 1 {
					/*If the octet has at least two remaining grids, compare within the octet, and readjust
					the bounds if necessary.*/
					if v > u+1 {
						singleStart := time.Now().UnixNano()
						boolArray[i] = compareGridBoolSingle(array, margin, i, boolArray[i], u, v)
						if (boolArray[i]>>u)%2 == 0 {
							u = uint32(firstSet(boolArray[i]))
							for u > 0 && (i<<3)+u >= arrayLen {
								u--
							}
							for u > 0 && (boolArray[i]>>u)%2 == 0 {
								u--
							}
						}
						if (boolArray[i]>>(v-1))%2 == 0 {
							v = uint32(lastSet(boolArray[i], uint8(u+1)))
							for v > u && (i<<3)+(v-1) >= arrayLen {
								v--
							}
							for v > u && (boolArray[i]>>(v-1))%2 == 0 {
								v--
							}
						}
						singleEnd := time.Now().UnixNano()
						singleTime += (singleEnd - singleStart)
					}
					/*Unlike comparing within a single octet, comparison across
					octets does not require any of them have multiple grids
					remaining.*/
					doubleStart := time.Now().UnixNano()
					gv := array[(i<<3)+(v-1)]
					var j uint32
					/*Find the last grid "in reach" of the last one in the current octet.*/
					if gv.avgLuma >= 255-margInt {
						j = mostComparableCursor(array, i<<3, arrayLen, gv.w, gv.h, 255)
					} else {
						j = mostComparableCursor(array, i<<3, arrayLen, gv.w, gv.h, gv.avgLuma+margInt)
					}
					j >>= 3

					/*Decrement if the search went out of bounds or it landed on an octet
					whose grids have all been eliminated.*/
					for j >= boolLen || (boolArray[j] == 0 && j > i+1) {
						j--
					}

					/*If at least octet has at least one grid that is comparable to at least
					one in the current octet, make comparisons.*/
					if j > i+1 {
						compareDoubles(boolArray, i, j, array, u, v, margin, tNum)
					}
					doubleEnd := time.Now().UnixNano()
					doubleTime += (doubleEnd - doubleStart)
				}
			}
		}
	}

	/*Shuffle around the grids so that all the remaining ones are at
	the beginning and all eliminated ones are at the end.*/
	restructuredBoolArray(boolArray, boolLen, array, arrayLen)
	fmt.Println("Time to compare single octets: ")
	printTime(singleTime)
	fmt.Println("Time to compare across octets: ")
	printTime(doubleTime)
	return array
}

/*This generates a grid from a fragment of a monochrome image.*/
func gridFromImg(img [][]uint8, x1 uint32, x2 uint32, y1 uint32, y2 uint32) Grid {
	if x1 == x2 || y1 == y2 {
		panic("Empty grid produced during extraction process")
	}

	/*Swap coordinates in order to avoid underflow*/
	if x1 > x2 {
		x1, x2 = x2, x1
	}
	if y1 > y2 {
		y1, y2 = y2, y1
	}

	if x2-x1 > 255 || y2-y1 > 255 {
		panic("Dimensions above 255 not supported")
	}

	g := Grid{w: uint8(x2 - x1), h: uint8(y2 - y1)}
	h32 := uint32(g.h)
	w32 := uint32(g.w)
	g.array = make([][]uint8, g.w)
	g.maxLuma = 0
	g.minLuma = 255
	sum := uint32(0)

	/*Get a pixel from the image, determine whether
	it is higher or lower than previous pixels, add
	it to the sum, and then place it into the grid.*/
	for i := uint32(0); i < w32; i++ {
		g.array[i] = make([]uint8, g.h)
		for j := uint32(0); j < h32; j++ {
			p := img[x1+i][y1+j]
			if p > g.maxLuma {
				g.maxLuma = p
			}
			if p < g.minLuma {
				g.minLuma = p
			}
			sum += uint32(p)
			g.array[i][j] = p
		}
	}

	g.avgLuma = uint8(sum / (h32 * w32))

	return g
}

/*
Get the xy coordinates from a tree in order to
create grids.
*/
func coordsFromTree(t *Tree, coordArray [][]uint32, index uint32) {
	/*If the tree is in fact a leaf, it place its
	coordinates into the array*/
	if t.hasChildren == 0 {
		if coordArray[index] != nil && len(coordArray[index]) != 0 {
			panic("Already set\n")
		}
		coordArray[index] = make([]uint32, 4)
		coordArray[index][0] = t.x1
		coordArray[index][1] = t.x2
		coordArray[index][2] = t.y1
		coordArray[index][3] = t.y2
		return
	}
	/*Otherwise, find leaves while offsetting the index when
	appropriate.*/
	if t.hasChildren&1 != 0 {
		coordsFromTree(t.rTree, coordArray, index)
	}
	if (t.hasChildren>>1)&1 != 0 {
		coordsFromTree(t.lTree, coordArray, index+uint32(t.rTree.leafNum))
	}
}

/*Get the coordinates from an array of images along with
a corresponding array of trees.*/
/*Making an array with a predefined size after receiving
all images reduces garbage collection time.*/
func gridsFromCoords(img [][][]uint8, trees []*Tree) []Grid {
	/*The total numebr of leaves will determine the number of coordinate sets.*/
	totalLeafNum := 0
	for i := 0; i < len(trees); i++ {
		totalLeafNum += trees[i].leafNum
	}

	/*Create an array of coorindates and populate them based on the trees.*/
	coordArray := make([][]uint32, totalLeafNum)
	tempLeafNum := uint32(0)
	for i := 0; i < len(trees); i++ {
		fmt.Printf("%d/%d\n", i, len(trees))
		coordsFromTree(trees[i], coordArray, tempLeafNum)
		l := uint32(trees[i].leafNum)
		//sort.Slice(coordArray, func(i, j int) bool { return j < int(tempLeafNum) || i >= int(tempLeafNum+l) || coordArray[j][1]-coordArray[j][0] > coordArray[i][1]-coordArray[i][0] || (coordArray[j][1]-coordArray[j][0] == coordArray[i][1]-coordArray[i][0] && coordArray[j][3]-coordArray[j][2] > coordArray[i][3]-coordArray[i][2])})
		tempLeafNum += l
	}

	/*Create and populate the grid array based on the coordinates*/
	gridArray := make([]Grid, totalLeafNum)
	tempLeafNum = 0
	for i := 0; i < len(img); i++ {
		fmt.Printf("%d/%d\n", i, len(img))
		leafNum := uint32(trees[i].leafNum)
		for j := uint32(0); j < leafNum; j++ {
			gridArray[tempLeafNum+j] = gridFromImg(img[i], coordArray[tempLeafNum+j][0], coordArray[tempLeafNum+j][1], coordArray[tempLeafNum+j][2], coordArray[tempLeafNum+j][3])
		}
		tempLeafNum += leafNum
	}
	return gridArray
}

/*This adds a grid and its coordinates in an image to a map.*/
func mapFromTree(gridMap map[uint32]Grid, img [][]uint8, t *Tree) map[uint32]Grid {
	if t.hasChildren == 0 {
		gridMap[(t.x1<<16)|(t.y1&65535)] = gridFromImg(img, t.x1, t.x2, t.y1, t.y2)
	}
	if t.hasChildren&1 != 0 {
		gridMap = mapFromTree(gridMap, img, t.rTree)
	}
	if (t.hasChildren>>1)&1 != 0 {
		gridMap = mapFromTree(gridMap, img, t.lTree)
	}
	return gridMap
}

/*
This finds the first cursor in a grid array that fits one aspect of
a grid used as a search term.
*/
func firstCursor(array []Grid, g Grid, key uint8, n1 uint32, n2 uint32) uint32 {
	/*
		0	w
		1	h
		2	w+1
		3	h+1
		4	avgLuma
		5	whole grid
	*/
	for n1 < n2 {
		m := uint32((n1 + n2) / 2)
		if (key == 0 && array[m].w >= g.w) ||
			(key == 1 && array[m].w >= g.w+1) ||
			(key == 2 && array[m].h >= g.h) ||
			(key == 3 && array[m].h >= g.h+1) ||
			(key == 4 && array[m].avgLuma >= g.avgLuma) ||
			(key == 5 && lessGrid(g, array[m], false)) {
			n2 = m
		} else {
			n1 = m + 1
		}
	}
	return n1
}

/*
This function breaks down an image into individual parts and traces them into a new image
using the most similar fragments of images previously processed. It is the primary reason
this program exists.
*/
func lumaTrace(img [][]uint8, ymg [][]uint8, array []Grid, arrayLen uint32, t *Tree, tNum uint32) [][]uint8 {
	gridMap := make(map[uint32]Grid)
	/*This takes in an image (or a monochrome representation of one) along with a tree to
	subdivide it, and puts the grids created from the subdivisions and their coordinates in
	a map.*/
	gridMap = mapFromTree(gridMap, img, t)
	/*This stores the top-right corner of every grid.*/
	keys := make([]uint32, t.leafNum)
	kLen := 0
	for key := range gridMap {
		keys[kLen] = key
		kLen++
	}
	/*This sorts the coordinates such that the earlier entries refer to those grids which
	would be sorted earlier (because of being narrow, short, or dark on average).*/
	sort.SliceStable(keys, func(i, j int) bool { return lessGrid(gridMap[keys[i]], gridMap[keys[j]], false) })
	/*This finds the entry in the array that is as short, narrow, and dark as the shortest,
	narrowest, and darkest grid in the map.*/
	w1 := firstCursor(array, gridMap[keys[0]], 0, 0, uint32(len(array)))
	w2 := firstCursor(array, gridMap[keys[0]], 1, w1, uint32(len(array)))
	h1 := firstCursor(array, gridMap[keys[0]], 2, w1, w2)
	h2 := firstCursor(array, gridMap[keys[0]], 3, h1, w2)
	a := firstCursor(array, gridMap[keys[0]], 5, h1, h2)
	/*This parameterizes the dimensions of the grid, which will be used often in the following
	loop.*/
	gw := gridMap[keys[0]].w
	gh := gridMap[keys[0]].h
	aw, ah := gw, gh
	for i := 0; i < t.leafNum; i++ {
		if 1000000000 < time.Now().UnixNano()-start {
			fmt.Printf("%f%%\n", 100.0*float64(i)/float64(t.leafNum))
			start = time.Now().UnixNano()
		}
		g := gridMap[keys[i]]
		gw = g.w
		gh = g.h
		/*This loop restricts its search to just those grids from the array that are
		the same dimensions as the one from the map currently being examined. The
		dimensions from the array are reparameterized at the end and the ones from
		the map at the beginning, allowing for a mismatch to be found. If that is the
		case, the following if statement readjusts the endpoints for the search terms.*/
		if aw != gw || ah != gh {
			h_a := w1
			h_b := w2
			if gw != aw {
				if aw < gw {
					w2 = firstCursor(array, g, 1, a, uint32(len(array)))
					w1 = firstCursor(array, g, 0, a, w2)
				} else {
					w1 = firstCursor(array, g, 0, 0, a)
					w2 = firstCursor(array, g, 1, w1, a)
				}
				h_a = w1
				h_b = w2
			} else {
				if ah < gh {
					h_a = a
				} else {
					h_b = a
				}
			}
			h1 = firstCursor(array, g, 2, h_a, h_b)
			h2 = firstCursor(array, g, 3, h1, h_b)
			a = firstCursor(array, g, 5, h1, h2)
		}
		minDiffC := a
		minDiffInt := uint8(gridDiff(array[a], g) / (uint32(g.w) * uint32(g.h)))
		/*The program guesses based on previous information and restricts
		its search to grids that have a mathematic possibility of being
		more accurate.*/
		l1 := h1
		if g.avgLuma > minDiffInt {
			n1 := h1
			n2 := h2
			for n1 < n2 {
				m := uint32((n1 + n2) / 2)
				if array[m].avgLuma > g.avgLuma-minDiffInt {
					n2 = m
				} else {
					n1 = m + 1
				}
			}
			l1 = n1
		}
		l2 := h2
		if g.avgLuma < 255-minDiffInt {
			n1 := l1
			n2 := h2
			for n1 < n2 {
				m := uint32((n1 + n2) / 2)
				if array[m].avgLuma > g.avgLuma+minDiffInt {
					n2 = m
				} else {
					n1 = m + 1
				}
			}
			l2 = n2
		}
		wg.Add(int(tNum))
		for k := uint32(0); k < tNum; k++ {
			go func(k uint32) {
				defer wg.Done()
				/*Each core will cover a different segment of the array before and after the initial guess.
				If there is no mathematical way for even the beginning of the segment in question to be
				more similar to the grid in the map vis a vis the most similar thus far found, the for loop
				below simply doesn't start. If it might be, it looks at each grid in the segment, and only
				when demonstrating there is mathematically enough similarity to the grid in the map to
				warrant a comparison, checks to see if the grid is more similar. These levels of gatekeeping
				solved a bottleneck that previously caused an image to take minutes to trace.*/
				loopStart := a + (k * (l2 - a) / tNum) + 1
				loopEnd := a + (((k + 1) * (l2 - a)) / tNum) - ((k + 1) / tNum)
				for j := loopStart; j <= loopEnd; j++ {
					if byteAbsDiff(g.avgLuma, array[j].avgLuma) < minDiffInt && (g.maxLuma > 255-minDiffInt || array[j].minLuma < g.maxLuma+minDiffInt) && (array[j].maxLuma > 255-minDiffInt || g.minLuma < array[j].maxLuma+minDiffInt) {
						crossRange := getCrossRange(array[j], g)
						var diffTemp uint32
						if crossRange >= minDiffInt {
							diffTemp = gridDiffAlt(array[j], g, minDiffInt, crossRange)
						} else {
							diffTemp = uint32(crossRange) * uint32(g.w) * uint32(g.h)
						}
						if diffTemp < uint32(minDiffInt)*uint32(g.w)*uint32(g.h) {
							minDiffInt = uint8(diffTemp / (uint32(g.w) * uint32(g.h)))
							minDiffC = j
							//minDiffInt = uint8(minDiff*256.0)
						}
					}
				}
				loopStart = a - (k * (a - l1) / tNum) - 1
				loopEnd = a - (((k + 1) * (a - l1)) / tNum)
				for j := loopStart; j >= loopEnd; j-- {
					if byteAbsDiff(g.avgLuma, array[j].avgLuma) < minDiffInt && (g.maxLuma > 255-minDiffInt || array[j].minLuma < g.maxLuma+minDiffInt) && (array[j].maxLuma > 255-minDiffInt || g.minLuma < array[j].maxLuma+minDiffInt) {
						crossRange := getCrossRange(array[j], g)
						var diffTemp uint32
						if crossRange >= minDiffInt {
							diffTemp = gridDiffAlt(array[j], g, minDiffInt, crossRange)
						} else {
							diffTemp = uint32(crossRange) * uint32(g.w) * uint32(g.h)
						}
						if diffTemp < uint32(minDiffInt)*uint32(g.w)*uint32(g.h) {
							minDiffInt = uint8(diffTemp / (uint32(g.w) * uint32(g.h)))
							minDiffC = j
							//minDiffInt = uint8(minDiff*256.0)
						}
					}
				}
			}(k)
		}
		wg.Wait()
		/*The coordinates are stored in the map, in a way involving bitwise operations. This simply
		reverses those operations to get separate x and y values.*/
		x1 := keys[i] >> 16
		x2 := x1 + uint32(gw)
		y1 := keys[i] & 65535
		y2 := y1 + uint32(gh)
		for x := x1; x < x2; x++ {
			if int(x) > len(ymg) || minDiffC > uint32(len(array)) || int(x-x1) > len(array[minDiffC].array) {
				panic("Variables pointing to outside the array produced during luma trace.")
			}
			copy(ymg[x][y1:y2], array[minDiffC].array[x-x1])
		}
		/*This uses the index of the most similar grid from this iteration of the loop as a guess for
		the next time.*/
		a = minDiffC
		aw = array[a].w
		ah = array[a].h
	}
	return ymg
}

/*Read a grid array from a file.*/
func readFromFile(fName string) ([]Grid, error) {
	f, err := os.Open(fName)
	if nil != err {
		fmt.Println(err)
		return nil, err
	}
	defer f.Close()
	br := bufio.NewReader(f)
	/*Generate a six-byte string with the little-endian size*/
	sizeStr := make([]uint8, 6)
	for i := 0; 6 > i; i++ {
		sStr, err := br.ReadByte()
		if nil != err {
			fmt.Println(err)
			return nil, err
		}
		sizeStr[5-i] = sStr
	}
	/*Calculate the size*/
	size := 0
	for i := 0; 6 > i; i++ {
		size = (size * 256) + int(sizeStr[i])
	}
	/*For each grid, get the width, height, and pixel data, one-by-one.*/
	array := make([]Grid, size)
	for i := 0; i < size; i++ {
		w, err := br.ReadByte()
		if nil != err {
			fmt.Println(err)
			return nil, err
		}
		h, err := br.ReadByte()
		if nil != err {
			fmt.Println(err)
			return nil, err
		}
		if w != 0 && h != 0 {
			g := Grid{w: w, h: h, maxLuma: 0, minLuma: 255, avgLuma: 128}
			sum := uint32(0)
			g.array = make([][]uint8, w)
			var x, p uint8
			for x = 0; x < w; x++ {
				g.array[x] = make([]uint8, h)
				for y := byte(0); y < h; y++ {
					p, err = br.ReadByte()
					if nil != err {
						fmt.Println(err)
						return nil, err
					}
					if p > g.maxLuma {
						g.maxLuma = p
					}
					if p < g.minLuma {
						g.minLuma = p
					}
					sum += uint32(p)
					g.array[x][y] = p
				}
			}
			g.avgLuma = uint8(sum / (uint32(w) * uint32(h)))
			//g.resetLuma()
			array[i] = g
		} else {
			panic("Empty grid found while reading from file")
		}
	}
	sort.Slice(array, func(i, j int) bool { return lessGrid(array[i], array[j], false) })
	return array, nil
}

/*Write the grid array to a file.*/
func writeToFile(array []Grid, arrayLen uint32, fName string) error {
	/*Predefining array size to reduce garbage collection time*/
	byte_array := make([]byte, 6+(arrayLen*uint32(2+(int(array[arrayLen-1].w)*int(array[arrayLen-1].h)))))
	/*Write the size of the array as a little-endian byte array.*/
	for i := 0; 6 > i; i++ {
		c := uint8((arrayLen >> (8 * i)) % 256)
		byte_array[i] = byte(c)
	}
	cursor := uint32(6)
	/*Write the dimensions of each grid, followed by its pixels*/
	for i := uint32(0); i < arrayLen; i++ {
		if array[i].w == 0 || array[i].h == 0 {
			panic("Empty grid found while writing to file")
		}
		byte_array[cursor] = byte(array[i].w)
		byte_array[cursor+1] = byte(array[i].h)
		h32 := uint32(array[i].h)
		w32 := uint32(array[i].w)
		for j := uint32(0); j < w32; j++ {
			for k := uint32(0); k < h32; k++ {
				byte_array[cursor+2+(j*h32)+k] = byte(array[i].array[j][k])
			}
		}
		cursor += (2 + (w32 * h32))
	}
	return os.WriteFile(fName, byte_array[:cursor], 0777)
}

/*Combine two arrays.*/
func combineArrays(array1 []Grid, array2 []Grid, margin float64, tNum uint32) []Grid {
	array1 = append(array1, array2...)
	sort.Slice(array1, func(i, j int) bool { return lessGrid(array1[i], array1[j], false) })
	start = time.Now().UnixNano()
	array1 = removeRedundantGrids(array1, margin, tNum)
	return array1
}

/*Generate an image object from an image file.*/
func openImage(path string) (image.Image, error) {
	f, err := os.Open(path)
	if nil != err {
		fmt.Println(err)
		return nil, err
	}
	defer f.Close()
	/*Handle PNG files specially, for reasons I cannot ascertain.*/
	if strings.HasSuffix(strings.ToLower(path), ".png") {
		pngImg, err := png.Decode(f)
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

/*Convert an image to monocrhome and store it in an integer array*/
func convertToGrayscale(img image.Image, w int, h int, tNum uint32) [][]uint8 {
	mono := make([][]uint8, w)
	tNumAct := tNum
	colPer := 1
	if w > int(tNum) {
		colPer = w / int(tNum)
	} else if uint32(w) < tNum {
		tNumAct = uint32(w)
	}
	/*Simply drop in the grayscale values for an image that is
	already monochrome.*/
	if strings.HasSuffix(strings.ToLower(reflect.TypeOf(img).String()), "gray") {
		wg.Add(int(tNumAct))
		for t := uint32(0); t < tNumAct; t++ {
			go func(t uint32) {
				defer wg.Done()
				for x := 0; x < colPer; x++ {
					mono[x+(int(t)*colPer)] = make([]uint8, h)
					for y := 0; y < h; y++ {
						l, _, _, _ := img.At(x+(int(t)*colPer), y).RGBA()
						mono[x+(int(t)*colPer)][y] = uint8(l >> 8)
					}
				}
			}(t)
		}
		wg.Wait()
	} else {
		/*Use basic color math to generate grayscale values*/
		wg.Add(int(tNumAct))
		for t := uint32(0); t < tNumAct; t++ {
			go func(t uint32) {
				defer wg.Done()
				for x := 0; x < colPer; x++ {
					mono[x+(int(t)*colPer)] = make([]uint8, h)
					for y := 0; y < h; y++ {
						r, g, b, _ := img.At(x+(int(t)*colPer), y).RGBA()
						r >>= 8
						g >>= 8
						b >>= 8
						mono[x+(int(t)*colPer)][y] = grayscale(uint8(r), uint8(g), uint8(b))
					}
				}
			}(t)
		}
		wg.Wait()
	}
	return mono
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

/*
Creates an image whose brightness is based on the result of a luma trace and
whose color is based on the original image
*/
func colorize(img image.Image, array1 [][]uint8, array2 [][]uint8, w int, h int) image.Image {
	imgType := strings.ToLower(reflect.TypeOf(img).String())
	/*This section is for grayscale output.*/
	tp := uint8(16)
	if strings.HasSuffix(imgType, "gray") {
		ymg := image.NewGray(image.Rectangle{image.Point{0, 0}, image.Point{w, h}})
		for x := 0; x < w; x++ {
			for y := 0; y < h; y++ {
				ln := array2[x][y]
				gray := array1[x][y]
				for byteAbsDiff(ln, gray) > tp {
					ln = (ln >> 1) + (gray >> 1) + (1 & ln & gray)
				}
				ymg.SetGray(x, y, color.Gray{ln})
			}
		}
		return ymg
	}
	/*Currently, only monochrome and RGBA images are supported.*/
	if strings.HasSuffix(imgType, "rgba") || strings.HasSuffix(imgType, "paletted") {
		ymg := image.NewRGBA(image.Rectangle{image.Point{0, 0}, image.Point{w, h}})
		for x := 0; x < w; x++ {
			for y := 0; y < h; y++ {
				r, g, b, _ := img.At(x, y).RGBA()
				r >>= 8
				g >>= 8
				b >>= 8
				/*The loop multiplies the original RGB values by the ratio of the luma trace to the
				original brightness value, unless the pixel is black or close enough to gray.*/
				/*Regardless, loops are used to bring errant shades closer to the base image, to
				prevent blotching.*/
				ln := array2[x][y]
				if (r > 0 || g > 0 || b > 0) && 100*minUint32(r, minUint32(g, b)) < 95*maxUint32(r, maxUint32(g, b)) {
					ratio := float64(ln) / float64(array1[x][y])
					r_ := uint8(ratio * float64(r))
					for byteAbsDiff(r_, uint8(r)) > tp {
						r_ = (r_ >> 1) + (uint8(r) >> 1) + (1 & r_ & uint8(r))
					}
					g_ := uint8(ratio * float64(g))
					for byteAbsDiff(g_, uint8(g)) > tp {
						g_ = (g_ >> 1) + (uint8(g) >> 1) + (1 & g_ & uint8(g))
					}
					b_ := uint8(ratio * float64(b))
					for byteAbsDiff(b_, uint8(b)) > tp {
						b_ = (b_ >> 1) + (uint8(b) >> 1) + (1 & b_ & uint8(b))
					}
					ymg.SetRGBA(x, y, color.RGBA{r_, g_, b_, 255})
				} else {
					gray := array1[x][y]
					for byteAbsDiff(ln, gray) > tp {
						ln = (ln >> 1) + (gray >> 1) + (1 & ln & gray)
					}
					ymg.SetRGBA(x, y, color.RGBA{ln, ln, ln, 255})
				}
			}
		}
		return ymg
	}
	return nil
}

func main() {
	rand.Seed(time.Now().UnixNano())
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
	var arrayLen uint32
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
			fmt.Println("	-t	Set number of threads, default 1.")
			fmt.Println("	-x	Output to standard output, to use the input with other prorams. Cannot be used with -y or -k, and must have -i or -l specify input data.")
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
			fmt.Println("Insufficient arguments, please specify either an output image using -o, an output dataset using -k, or print to standard output with -x")
		}
		return
	}
	if len(kArray) > 0 && len(iArray) == 0 && len(lArray) == 0 {
		fmt.Println("Output dataset specified without specifying input image using -i or input dataset using -l")
		return
	}
	if len(oArray) > 0 && (len(yArray) == 0 || len(lArray) == 0 || len(iArray) == 0) {
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
		fmt.Println("Base image specified without output image specified with -o or standard output with -x")
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
	if len(yArray) > 0 && len(yArray) < 3 {
		fmt.Println("Please specify at least one base image file, minimum and maximum grid dimensions, in that exact order.")
		return
	}
	if len(tArray) > 1 {
		fmt.Println("Please specify one argument for thread number.")
		return
	}
	/*This handles inputting one or more file containing a grid array.*/
	tNum := uint32(1)
	if len(tArray) == 1 {
		tNum, err := strconv.ParseUint(tArray[0], 10, 8)
		if err != nil {
			fmt.Println("Please specify an integer for thread number")
			log.Fatal(err)
			return
		}
		if tNum < 1 {
			fmt.Println("Please specify a positive integer for thread number")
			return
		}
	}
	if len(lArray) > 0 {
		fmt.Println("Adding data from " + lArray[0])
		arrayTemp, err := readFromFile(lArray[0])
		if nil != err {
			fmt.Println("Please specify valid filenames for all input datasets.")
			log.Fatal(err)
			return
		}
		array = arrayTemp
		arrayLen = uint32(len(array))
		for i := uint32(0); i < arrayLen; i++ {
			for array[i].w < 1 || array[i].h < 1 {
				array = append(array[:i], array[i+1:]...)
				arrayLen--
			}
		}
		fmt.Printf("%v\n", len(array))
		/*If there are multiple arguments for -l, a margin must go at the end, following
		VALID filenames.*/
		if len(lArray) > 2 {
			margin, err := strconv.ParseFloat(lArray[len(lArray)-1], 64)
			if nil != err {
				fmt.Println("Please specify margin AFTER all input datasets.")
				log.Fatal(err)
				return
			}
			for i := 1; i < len(lArray)-1; i++ {
				fmt.Println("Adding data from " + lArray[i])
				arrayTemp, err := readFromFile(lArray[i])
				if nil != err {
					fmt.Println("Please specify valid filenames for all input datasets.")
					log.Fatal(err)
					return
				}
				arrayLen := uint32(len(arrayTemp))
				for i := uint32(0); i < arrayLen; i++ {
					for arrayTemp[i].w < 1 || arrayTemp[i].h < 1 {
						arrayTemp = append(arrayTemp[:i], arrayTemp[i+1:]...)
						arrayLen--
					}
				}
				array = combineArrays(array, arrayTemp, margin, tNum)
				n1 := uint32(0)
				n2 := uint32(len(array))
				var m uint32
				for n1 < n2 {
					m = n1 + ((n2 - n1) >> 1)
					if array[m].w == 0 || array[m].h == 0 {
						n2 = m
					} else {
						n1 = m + 1
					}
				}
				arrayLen = n1
				fmt.Printf("%v\n", arrayLen)
			}
		}
	}
	/*This handles inputting one or more images for the purposes of creating grid arrays.*/
	if len(iArray) > 0 {
		minIn, errMin := strconv.ParseUint(iArray[len(iArray)-3], 10, 8)
		maxIn, errMax := strconv.ParseUint(iArray[len(iArray)-2], 10, 8)
		/*There are a lot of issues that crop up when the maximum is less than twice the
		minimum, and until I hammer those out, this constraint will remain.*/
		if maxIn < minIn*2 {
			fmt.Println("Please specify a maximum size at least twice that of the minimum size.")
			return
		}
		margin, errMarg := strconv.ParseFloat(iArray[len(iArray)-1], 64)
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
		imgArray := make([][][]uint8, len(iArray)-3)
		trees := make([]*Tree, len(iArray)-3)
		monoTime := int64(0)
		for i := 0; i < len(iArray)-3; i++ {
			monoStart := time.Now().UnixNano()
			img, err := openImage(iArray[i])
			if nil != err {
				fmt.Println("Please specify valid filenames for all input images.")
				log.Fatal(err)
				return
			}
			fmt.Printf("Reading %s\n", iArray[i])
			imgBnd := img.Bounds()
			w := imgBnd.Max.X
			h := imgBnd.Max.Y
			imgArray[i] = convertToGrayscale(img, w, h, tNum)
			monoTime += (time.Now().UnixNano() - monoStart)
			trees[i] = generateTree(0, uint32(w), 0, uint32(h), uint8(minIn), uint8(maxIn))
			start = time.Now().UnixNano()
		}
		fmt.Printf("Time taken to intercept and decolorize images: ")
		printTime(monoTime)
		fmt.Printf("Creating grids from images\n")
		gridCrStart := time.Now().UnixNano()
		array = gridsFromCoords(imgArray, trees)
		gridCrEnd := time.Now().UnixNano()
		fmt.Printf("Creation of grids complete: \n")
		printTime(gridCrEnd - gridCrStart)
		fmt.Printf("Sorting started\n")
		sort.Slice(array, func(i, j int) bool { return lessGrid(array[i], array[j], false) })
		fmt.Printf("Sorting completed\n")
		if margin > 0 {
			//origSize := len(array);
			fmt.Println("Removing redundant grids")
			start = time.Now().UnixNano()
			array = removeRedundantGrids(array, margin, tNum)
			n1 := uint32(0)
			n2 := uint32(len(array))
			var m uint32
			for n1 < n2 {
				m = n1 + ((n2 - n1) >> 1)
				if array[m].w == 0 || array[m].h == 0 {
					n2 = m
				} else {
					n1 = m + 1
				}
			}
			arrayLen = n1
			/*end := time.Now().UnixNano()
			fmt.Println("Go reduction: ")
			printTime(end-start)
			cArray := cGridArray(array)
			start = time.Now().UnixNano()
			cArray = C.reducedArray(cArray, C.uint(len(array)), C.float(margin))*/
			end := time.Now().UnixNano()
			/*C.freeGridArray(cArray, C.gridArraySize(cArray, C.ulong(0), C.ulong(origSize)));
			fmt.Println("C reduction: ")
			printTime(end-start)*/
			timeTotal := (end - startTemp)
			printTime(timeTotal)
		}
	}
	/*This handles the luma trace, which breaks an image or image sequence down into
	parts and replaces them with the most simlar grid in a stored array.*/
	/*
		One input image		presence of digit string irrelevant, add extension if not present
		Multiple input images	if digit string present and no extension in output, distribut*/
	if 3 <= len(yArray) {
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
		leadingZeroes := uint8(0)
		outputPrefix := ""
		outputSuffix := ""
		outputFileNames := make([]string, len(yArray)-2)
		commonImageFormats := [6]string{"PNG", "JPG", "JPEG", "BMP", "TIFF", "GIF"}
		cifLength := len(commonImageFormats)
		foundExt := int8(0)
		if len(yArray) == 3 {
			for i := 0; i < cifLength; i++ {
				if strings.HasSuffix(strings.ToUpper(oArray[0]), fmt.Sprintf("%s%s", ".", commonImageFormats[i])) {
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
				for i := 0; i < cifLength; i++ {
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
				for i := 0; i < len(yArray)-2; i++ {
					for j := 0; j < cifLength; j++ {
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
					} else if int(k) < cifLength-1 {
						fmt.Println("Multiple extensions found among input files. Defaulting to PNG for output.")
						outputSuffix += ".png"
					}
					/*The input filenames do not collectively invlude any (common) file extensions.*/
				} else {
					fmt.Println("No valid extensions found among input files.")
					return
				}
			}
			for i := 0; i < len(yArray)-2; i++ {
				numStr := fmt.Sprintf("%d", i)
				for len(numStr) < int(leadingZeroes) {
					numStr = fmt.Sprintf("%s%s", "0", numStr)
				}
				outputFileNames[i] = fmt.Sprintf("%s%s%s", outputPrefix, numStr, outputSuffix)
			}
		}
		for i := 0; i < len(yArray)-2; i++ {
			for j := 0; j < len(yArray)-2; j++ {
				if strings.Compare(outputFileNames[i], yArray[j]) == 0 {
					fmt.Println("Setting output file name to input file name not permitted.")
					return
				}
			}
		}
		for i := 0; i < len(yArray)-2; i++ {
			img, err := openImage(yArray[i])
			if nil != err {
				fmt.Println("Please specify valid filenames for every input image.")
				log.Fatal(err)
				return
			}
			imgBnd := img.Bounds()
			w := imgBnd.Max.X
			h := imgBnd.Max.Y
			t := generateTree(0, uint32(w), 0, uint32(h), uint8(minIn), uint8(maxIn))
			/*To make things simpler, all images are converted to monochrome and stored in an
			array of 8-bit numbers. Color is restored in the resulting image.*/
			mono := convertToGrayscale(img, w, h, tNum)
			monoNew := make([][]uint8, w)
			for i := 0; i < w; i++ {
				monoNew[i] = make([]uint8, h)
				for j := 0; j < h; j++ {
					monoNew[i][j] = 0
				}
			}

			fmt.Println("Performing luma trace on " + yArray[i])
			start = time.Now().UnixNano()
			startTemp := start
			monoNew = lumaTrace(mono, monoNew, array, arrayLen, t, uint32(tNum))
			end := time.Now().UnixNano()
			printTime(end - startTemp)

			ymg := colorize(img, mono, monoNew, w, h)
			fmt.Println("Outputting to " + outputFileNames[i])
			outputF, err := os.Create(outputFileNames[i])
			if nil != err {
				log.Fatal(err)
				return
			}
			defer outputF.Close()
			png.Encode(outputF, ymg)
		}
	}
	if len(kArray) == 1 {
		writeToFile(array, arrayLen, kArray[0])
	}
}
