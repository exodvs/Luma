package main

import (
	"bufio"
	"fmt"
	"image"
	"image/color"
	"image/png"
	"log"
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

var pix = 0
var start = time.Now().UnixNano()
var arraySize = 0
var wg sync.WaitGroup

func byteAbsDiff(a uint8, b uint8) uint8 {
	if a > b {
		return a - b
	}
	return b - a
}

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
A struct for a grid, containing a width, height, average and median luma
and an array of luma values.
*/
type Grid struct {
	w       uint8
	h       uint8
	avgLuma uint8
	medLuma uint8
	maxLuma uint8
	minLuma uint8
	array   [][]uint8
}

/*This sets the luma value at a certain point in a grid.*/
func (g *Grid) setValue(x uint8, y uint8, value uint8) {
	g.array[x%g.w][y%g.h] = value
}

/*
This sets the average and median values of a Grid, usually upon
instantiation.
*/
func (g *Grid) resetLuma() {
	/*This array will eventually be sorted in order to find the
	median.*/
	arrayCopy := make([]uint8, g.w*g.h)
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
			arrayCopy[(i*g.h)+j] = g.array[i][j]
			sum += uint32(g.array[i][j])
		}
	}
	sort.Slice(arrayCopy, func(i, j int) bool { return arrayCopy[i] < arrayCopy[j] })
	g.medLuma = (uint8)(arrayCopy[g.h*g.w/2])
	g.avgLuma = (uint8)(sum / (uint32(g.h) * uint32(g.w)))
}

/*
This returns whether one grid is "less than" another grid. If two grids vary
in dimensions, the narrower or shorter one is less. Otherwise, if one is darker
on average, that one is less. Otherwise, if one has just one darker pixel,
counting from top-left to bottom-right, that one is less.
*/
func lessGrid(g1 Grid, g2 Grid) bool {
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
	return false
}

/*
This is a struct for a tree containing bounding x and y values, minimum
split values, children, and a two-bit variable to determine if it has
children.
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
	if t.x2-t.x1 > uint32(maxIn) && (t.y2-t.y1 <= uint32(maxIn) || 0 == rand.Uint32()%2) {
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
average.
*/
func gridDiff(g1 Grid, g2 Grid) float64 {
	if 0 != g1.w-g2.w || 0 != g1.h-g2.h {
		return 1.0
	}
	sum := uint32(0)
	for i := uint8(0); i < g1.w; i++ {
		for j := uint8(0); j < g1.h; j++ {
			sum += uint32(byteAbsDiff(g1.array[i][j], g2.array[i][j]))
		}
	}
	return float64(sum) / (256.0 * float64(g1.w*g1.h))
}
func gridDiffMax(g1 Grid, g2 Grid, maxIn uint8) uint8 {
	if g1.w != g2.w || g1.h != g2.h {
		return 1.0
	}
	maxDiff := uint8(0)
	w := g1.w
	h := g1.h
	for i := uint8(0); i < w && maxDiff < maxIn; i++ {
		for j := uint8(0); j < h && maxDiff < maxIn; j++ {
			c1 := g1.array[i][j]
			c2 := g1.array[i][j]
			diffTemp := uint8(0)
			if c1 > c2 {
				diffTemp = c1 - c2
			} else {
				diffTemp = c2 - c1
			}
			if diffTemp > maxDiff {
				maxDiff = diffTemp
			}
		}
	}
	return maxDiff
}

/*
This returns a maximum value if it is apparent that
the differences between two grids exceeds maxDiff before
a comparison is complete.
*/
func gridDiffAlt(g1 Grid, g2 Grid, maxDiff uint8) uint32 {
	if g1.w != g2.w || g1.h != g2.h {
		return 0xFFFFFFFF
	}
	if g2.maxLuma < uint8(255)-maxDiff && g1.minLuma > g2.maxLuma+maxDiff {
		return uint32(g1.w) * uint32(g1.h) * 255
	}
	if g1.maxLuma < uint8(255)-maxDiff && g2.minLuma > g1.maxLuma+maxDiff {
		return uint32(g1.w) * uint32(g1.h) * 255
	}
	sum := uint32(0)
	maxSum := uint32(maxDiff) * uint32(g1.w) * uint32(g1.h)
	w := g1.w
	h := g1.h
	for i := uint8(0); i < w && sum < maxSum; i++ {
		for j := uint8(0); j < h && sum < maxSum; j++ {
			c1 := g1.array[i][j]
			c2 := g2.array[i][j]
			if c1 > c2 {
				sum += uint32(c1 - c2)
			} else {
				sum += uint32(c2 - c1)
			}
		}
	}
	return sum
}

/*This is Brian Kernighan's bit-counting algorithm.*/
func kern(x uint8) int {
	count := 0
	for 0 != x {
		count += 1
		x &= (x - 1)
	}
	return count
}

func maxCornerDiff(g1 Grid, g2 Grid, maxIn uint8) uint8 {
	if g1.w != g2.w || g1.h != g2.h {
		return 255
	}
	ww := int(g1.w - 1)
	hh := int(g1.h - 1)
	maxCornerDiff := uint8(0)
	c1 := g1.array[0][0]
	c2 := g2.array[0][0]
	var diffTemp uint8
	if c1 > c2 {
		diffTemp = c1 - c2
	} else {
		diffTemp = c2 - c1
	}
	if diffTemp > maxIn {
		return diffTemp
	}
	if diffTemp > maxCornerDiff {
		maxCornerDiff = diffTemp
	}
	c1 = g1.array[0][hh]
	c2 = g2.array[0][hh]
	if c1 > c2 {
		diffTemp = c1 - c2
	} else {
		diffTemp = c2 - c1
	}
	if diffTemp > maxIn {
		return diffTemp
	}
	if diffTemp > maxCornerDiff {
		maxCornerDiff = diffTemp
	}
	c1 = g1.array[ww][0]
	c2 = g2.array[ww][0]
	if c1 > c2 {
		diffTemp = c1 - c2
	} else {
		diffTemp = c2 - c1
	}
	if diffTemp > maxIn {
		return diffTemp
	}
	if diffTemp > maxCornerDiff {
		maxCornerDiff = diffTemp
	}
	c1 = g1.array[ww][hh]
	c2 = g2.array[ww][hh]
	if c1 > c2 {
		diffTemp = c1 - c2
	} else {
		diffTemp = c2 - c1
	}
	if diffTemp > maxIn {
		return diffTemp
	}
	if diffTemp > maxCornerDiff {
		maxCornerDiff = diffTemp
	}
	return maxCornerDiff
}

func compareGridBoolSingle(array []Grid, margin float64, cursor uint32, octet uint8, u uint32, v uint32) uint8 {
	subset := octet
	if v < 8 {
		subset %= uint8(1 << v)
	}
	subset >>= uint8(u)
	/*Return the octet unchanged if there are fewer than two grids left to compare.*/
	if v <= u || v-u < 2 || kern(subset) < 2 {
		return octet
	}
	/*If two grids have different dimensions, compare separate parts of the octet.*/
	if array[(cursor<<3)|u].w != array[(cursor<<3)|(v-1)].w || array[(cursor<<3)|u].h != array[(cursor<<3)|(v-1)].h {
		uNew := u + 1
		for uNew < v && array[(cursor<<3)|u].w == array[(cursor<<3)|uNew].w && array[(cursor<<3)|u].h == array[(cursor<<3)|uNew].h {
			uNew++
		}
		return compareGridBoolSingle(array, margin, cursor, octet, u, uNew) &
			compareGridBoolSingle(array, margin, cursor, octet, uNew, v)
	}
	margInt := uint8(margin * 256.0)
	/*If two grids have very ddifferent average brightness levels, compare separate parts of the octet.*/
	if array[(cursor<<3)|(v-1)].avgLuma-array[(cursor<<3)|u].avgLuma >= margInt {
		uNew := v - 2
		vNew := u + 1
		for uNew > 1 && array[(cursor<<3)|(v-1)].avgLuma-array[(cursor<<3)|(uNew-1)].avgLuma < margInt {
			uNew--
		}
		for 0 == vNew>>3 && array[(cursor<<3)|vNew].avgLuma-array[(cursor<<3)|u].avgLuma < margInt {
			vNew++
		}
		if uNew > vNew {
			return compareGridBoolSingle(array, margin, cursor, octet, u, vNew) &
				compareGridBoolSingle(array, margin, cursor, octet, vNew, uNew) &
				compareGridBoolSingle(array, margin, cursor, octet, uNew, v)
		}
		return compareGridBoolSingle(array, margin, cursor, octet, u, uNew) &
			compareGridBoolSingle(array, margin, cursor, octet, uNew, vNew) &
			compareGridBoolSingle(array, margin, cursor, octet, vNew, v)
	}
	/*"We're in the endgame now.
	-Dr. Strange, Avengers: Infinity War (2018)*/
	for w1 := u; w1 < v-1; w1++ {
		if 1 == (uint32(octet)>>w1)%2 {
			a1 := array[(cursor<<3)|w1]
			for w2 := w1 + 1; 1 == (uint32(octet)>>w1)%2 && w2 < v; w2++ {
				if 1 == (octet>>w2)%2 {
					a2 := array[(cursor<<3)|w2]
					if maxCornerDiff(a1, a2, margInt) < margInt {
						range1 := a1.maxLuma - a1.minLuma
						range2 := a2.maxLuma - a2.minLuma
						if (range1 < margInt && range2 < margInt && gridDiffAlt(a1, a2, margInt) < uint32(margInt)*uint32(a1.w)*uint32(a1.h)) || (range1 > margInt && range2 > margInt && gridDiffMax(a1, a2, margInt) < margInt) {
							if 0 == rand.Uint32()%2 {
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
This takes in two bytes indicating remaining grids to be passed on in an array,
and eliminates redundancies.
*/
func compareGridBool(array []Grid, margin float64, cursor1 uint32, cursor2 uint32, bool1 uint8, bool2 uint8, u uint32, v uint32, u1 uint32, v1 uint32) uint16 {
	margInt := uint8(margin * 256.0)
	/*It is possible for either byte to be zeroed out, hence the first
	and second conditions in this for loop.*/
	for i := u; uint8(0) != bool1 && uint8(0) != bool2 && i < v; i++ {
		if uint8(1) == (bool1>>uint8(i))%uint8(2) {
			a1 := array[(cursor1<<3)|i]
			ww := int(a1.w)
			hh := int(a1.h)
			/*It is possible for the second byte to be zeroed out, or for the first bit
			currently being examined from the first byte to be unset, hence the first and
			second conditions of this for loop.*/
			for j := uint32(u1); uint8(0) != bool2 && uint8(1) == (bool1>>uint8(i))%uint8(2) && j < v1; j++ {
				wj := int(array[(cursor2<<3)|j].w)
				hj := int(array[(cursor2<<3)|j].h)
				/*This does not bother comparing two grids if they have different dimenisons, an average brightness
				far enough away from each other, or, obviously, if one of them has already been eliminated.*/
				if uint8(1) == (bool2>>uint8(j))%uint8(2) && ww == wj && hh == hj && array[(cursor2<<3)|j].avgLuma-a1.avgLuma < margInt {
					a2 := array[(cursor2<<3)|j]
					if maxCornerDiff(a1, a2, margInt) < margInt {
						/*In previous tests, sections with flat color tended to do better when grids were eliminated
						on the basis of overall average difference. Meanwhile, line-art and areas with more detail
						tended to do better when grids were eliminated on the basis of the most different set of pixels.
						The range variables below are used to elminate on the two bases.*/
						range1 := a1.maxLuma - a1.minLuma
						range2 := a2.maxLuma - a2.minLuma
						if (range1 < margInt && range2 < margInt && gridDiffAlt(a1, a2, margInt) < uint32(margInt)*uint32(a1.w)*uint32(a1.h)) || (range1 > margInt && range2 > margInt && gridDiffMax(a1, a2, margInt) < margInt) {
							if 0 == rand.Uint32()%2 {
								bool1 &= ^uint8(1 << i)
							} else {
								bool2 &= ^uint8(1 << j)
							}
						}
					}
				}
			}
		}
	}
	return (uint16(bool2) << 8) | uint16(bool1)
}

/*This eliminates grids that are similar */
func removeRedundantGrids(array []Grid, margin float64, tNum uint32) []Grid {
	arrayLen := uint32(len(array))
	total := 0
	/*The set of grids which will remain is expressed in an array of
	8-bit integers*/
	boolLen := (arrayLen / 8) + ((arrayLen % 2) | ((arrayLen / 2) % 2) | ((arrayLen / 4) % 2))
	/*if 1 == arrayLen%2 || 1 == (arrayLen/2)%2 || 1 == (arrayLen/4)%2 {
		boolLen++
	}*/
	boolArray := make([]uint8, boolLen)
	for i := uint32(0); i < boolLen; i++ {
		boolArray[i] = uint8(255)
	}
	if 0 != arrayLen&7 {
		boolArray[boolLen-1] = uint8((1 << (arrayLen & 7)) - 1)
	}
	singleX := int64(0)
	doubleX := int64(0)
	singleTime := int64(0)
	doubleTime := int64(0)
	/*This prevents the need to repeatedly recalculate.*/
	margInt := uint8(margin * 256.0)
	/*Every byte is internally compared, and bits are unset if they
	correspond to a grid that is too similar to a previous grid.
	Afterwards, each remaining grid described by the bit is compared
	to all subsequent grids of the same dimensions and similar
	average brightness level, unsetting bits if necessary. This ensures
	no pair of grids is compared twice.*/
	for i := uint32(0); i < boolLen; i++ {
		if 1000000000 < time.Now().UnixNano()-start {
			fmt.Printf("%f%%\n", 100.0*float64(i)/float64(arrayLen>>3))
			start = time.Now().UnixNano()
		}
		if 0 != boolArray[i] {
			/*For the time being, u and v are the first and last positions of set bits
			in a byte.*/
			u := uint32(0)
			for 0 == (boolArray[i]>>uint8(u))&1 {
				u++
			}
			v := u + 1
			for 0 == v>>3 && 0 != boolArray[i]>>uint8(v) {
				v++
			}
			if v > u+1 {
				singleStart := time.Now().UnixNano()
				boolArray[i] = compareGridBoolSingle(array, margin, i, boolArray[i], u, v)
				singleTime += (time.Now().UnixNano() - singleStart)
				singleX += 1
			}
			/*The earliest octet without grids comparable to the one at i is at endT*/
			a := i + 1
			b := boolLen
			for a < b {
				m := a + ((b - a) >> 1)
				if array[m<<3].w > array[(i<<3)|(v-1)].w || (array[m<<3].w == array[(i<<3)|(v-1)].w && array[m<<3].h > array[(i<<3)|(v-1)].h) || (array[m<<3].w == array[(i<<3)|(v-1)].w && array[m<<3].h == array[(i<<3)|(v-1)].h && array[m<<3].avgLuma-array[(i<<3)|(v-1)].avgLuma > margInt) {
					b = m
				} else {
					a = m + 1
				}
			}
			endT := a
			/*If there is at least one octet with grids comparable to those at i*/
			if endT > i+1 {
				/*"Remaining octets"*/
				remOct := endT - (i + 1)
				/*The number of octets that are left over when dividing the number of
				remaining octets by the number of threads. Remains 0 if the number of
				remaining octets is lesser than or evenly divisible by the number of
				threads.*/
				modT := uint32(0)
				/*"Actual thread number." Will be set to remOct if the number desginaged
				by the user is greater than remOct.*/
				tNumAct := tNum
				/*"Octet per " thread. Remains 1 only if tNum exceeds remOct.*/
				octPer := uint32(1)
				if remOct > tNum {
					modT = remOct % tNum
					octPer = remOct / tNum
				} else if remOct < tNum {
					tNumAct = remOct
				}
				wg.Add(int(tNumAct))
				/*Loops through the designated number of threads.*/
				for t := uint32(0); boolArray[i] != 0 && t < tNumAct; t++ {
					go func(t uint32) {
						defer wg.Done()
						/*Loops through the number of octets desgignated for a single thread.*/
						for j := uint32(0); boolArray[i] != 0 && j < octPer; j++ {
							if boolArray[(t*octPer)+j+i+1] != 0 {
								ii := (t * octPer) + j + i + 1
								u1 := uint32(0)
								for 0 == 1&(boolArray[ii]>>uint8(u1)) {
									u1++
								}
								if array[(ii<<3)|u1].w == array[(i<<3)|v].w && array[(ii<<3)|u1].h == array[(i<<3)|v].h && array[(ii<<3)|u1].avgLuma-array[(i<<3)|v].avgLuma < margInt {
									v1 := u1 + 1
									for boolArray[ii]>>v1 != 0 && array[(ii<<3)|v1].w == array[(i<<3)|v].w && array[(ii<<3)|v1].h == array[(i<<3)|v].h && array[(ii<<3)|v1].avgLuma-array[(i<<3)|v].avgLuma < margInt {
										v1++
									}
									doubleStart := time.Now().UnixNano()
									doublet := compareGridBool(array, margin, i, ii, boolArray[i], boolArray[ii], u, v, u1, v1)
									doubleTime += (time.Now().UnixNano() - doubleStart)
									doubleX += 1
									boolArray[i] = uint8(doublet % 256)
									boolArray[ii] = uint8(doublet >> 8)
								}
							}
						}
					}(t)
				}
				wg.Wait()
				if modT > 0 && boolArray[i] != 0 {
					wg.Add(int(modT))
					for t := endT - modT; boolArray[i] != 0 && t < endT; t++ {
						go func(t uint32) {
							defer wg.Done()
							if endT-modT+t < boolLen && boolArray[endT-modT+t] != 0 {
								u1 := uint32(0)
								for 0 == 1&(boolArray[endT-modT+t]>>u1) {
									u1++
								}
								ii := endT - modT + t
								if array[(ii<<3)|u1].w == array[(i<<3)|v].w && array[(ii<<3)|u1].h == array[(i<<3)|v].h && array[(ii<<3)|u1].avgLuma-array[(i<<3)|v].avgLuma < margInt {
									v1 := u1 + 1
									for 1 == 1&(boolArray[ii]>>v1) && array[(ii<<3)|v1].w == array[(i<<3)|v].w && array[(ii<<3)|v1].h == array[(i<<3)|v].h && array[(ii<<3)|v1].avgLuma-array[(i<<3)|v].avgLuma < margInt {
										v1++
									}
									doubleStart := time.Now().UnixNano()
									doublet := compareGridBool(array, margin, i, ii, boolArray[i], boolArray[ii], u, v, u1, v1)
									doubleTime += (time.Now().UnixNano() - doubleStart)
									doubleX += 1
									boolArray[i] = uint8(doublet % 256)
									boolArray[ii] = uint8(doublet >> 8)
								}
							}

						}(t)
					}
					wg.Wait()
				}
			}
		}
	}
	fmt.Printf("Single: %d	%d\n", singleTime, singleX)
	fmt.Printf("Double: %d	%d\n", doubleTime, doubleX)
	/*Remaining grids are added to a new array.*/
	for i := uint32(0); i < boolLen; i++ {
		total += kern(boolArray[i])
	}
	newArray := make([]Grid, total)
	newSize := 0
	for i := uint32(0); i < arrayLen; i++ {
		if 1 == (boolArray[i/8]>>(i%8))%2 {
			if 0 == array[i].w || 0 == array[i].h {
				panic("Empty grids found upon completion of elimination process.")
			}
			newArray[newSize] = array[i]
			newSize++
		}
	}
	if newSize != total {
		panic("Empty grids inserted into culled array")
	}
	return newArray
}

/*This generates a grid from a fragment of a monochrome image.*/
func gridFromImg(img [][]uint8, x1 uint32, x2 uint32, y1 uint32, y2 uint32) Grid {
	if x1 > x2 {
		x1, x2 = x2, x1
	}
	if y1 > y2 {
		y1, y2 = y2, y1
	}
	g := Grid{w: uint8(x2 - x1), h: uint8(y2 - y1)}
	if 0 == g.w || 0 == g.h {
		panic("Empty grid produced during extraction process")
	}
	g.array = make([][]uint8, g.w)
	for i := uint8(0); i < g.w; i++ {
		g.array[i] = make([]uint8, g.h)
		copy(g.array[i], img[x1+uint32(i)][y1:y2])
	}
	g.resetLuma()
	return g
}

/*Add fragments of an image to a grid array.*/
func gridsFromTree(img [][]uint8, t *Tree, array []Grid, margin float64, w int, h int) []Grid {
	/*This is used to tell the user how much of the image has been processed.*/
	if 1000000000 < time.Now().UnixNano()-start {
		fmt.Printf("%f%%\n", 100.0*float64(pix)/float64(w*h))
		start = time.Now().UnixNano()
	}
	/*If the tree has no children, create the grid and add it to the array.*/
	if 0 == t.hasChildren {
		array[arraySize] = gridFromImg(img, t.x1, t.x2, t.y1, t.y2)
		arraySize = arraySize + 1
		pix += int((t.x2 - t.x1) * (t.y2 - t.y1))
	}
	/*If the tree has children, go down the branches recursively.*/
	if 0 != t.hasChildren&1 {
		array = gridsFromTree(img, t.rTree, array, margin, w, h)
	}
	if 0 != (t.hasChildren>>1)&1 {
		array = gridsFromTree(img, t.lTree, array, margin, w, h)
	}
	return array
}

/*This adds a grid and its coordinates to a map.*/
func mapFromTree(gridMap map[uint32]Grid, img [][]uint8, t *Tree) map[uint32]Grid {
	if 0 == t.hasChildren {
		gridMap[(t.x1<<16)|(t.y1&65535)] = gridFromImg(img, t.x1, t.x2, t.y1, t.y2)
	}
	if 1 == t.hasChildren&1 {
		gridMap = mapFromTree(gridMap, img, t.rTree)
	}
	if 1 == 1&(t.hasChildren>>1) {
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
			(key == 5 && lessGrid(g, array[m])) {
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
func lumaTrace(img [][]uint8, ymg [][]uint8, array []Grid, t *Tree, tNum uint32) [][]uint8 {
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
	sort.SliceStable(keys, func(i, j int) bool { return lessGrid(gridMap[keys[i]], gridMap[keys[j]]) })
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
		minDiff := gridDiff(array[a], g)
		/*The program guesses based on previous information and restricts
		its search to grids that have a mathematic possibility of being
		more accurate.*/
		l1 := h1
		if g.avgLuma > uint8(minDiff*256.0) {
			n1 := h1
			n2 := h2
			for n1 < n2 {
				m := uint32((n1 + n2) / 2)
				if array[m].avgLuma > g.avgLuma-uint8(minDiff*256.0) {
					n2 = m
				} else {
					n1 = m + 1
				}
			}
			l1 = n1
		}
		l2 := h2
		if g.avgLuma < uint8((1.0-minDiff)*256.0) {
			n1 := l1
			n2 := h2
			for n1 < n2 {
				m := uint32((n1 + n2) / 2)
				if array[m].avgLuma > g.avgLuma+uint8(minDiff*256.0) {
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
					if byteAbsDiff(g.avgLuma, array[j].avgLuma) < uint8(minDiff*256.0) && (g.maxLuma > uint8((1.0-minDiff)*256.0) || array[j].minLuma < g.maxLuma+uint8(minDiff*256.0)) && (array[j].maxLuma > uint8((1.0-minDiff)*256.0) || g.minLuma < array[j].maxLuma+uint8(minDiff*256.0)) {
						diffTemp := gridDiffAlt(array[j], g, uint8(256.0*minDiff)) / (uint32(g.w) * uint32(g.h))
						if diffTemp < uint32(minDiff*256.0)*uint32(g.w)*uint32(g.h) {
							minDiff = float64(diffTemp) / 256.0
							minDiffC = j
						}
					}
				}
				loopStart = a - (k * (a - l1) / tNum) - 1
				if loopStart < 0 {
					loopStart = 0
				}
				loopEnd = a - (((k + 1) * (a - l1)) / tNum)
				for j := loopStart; j >= loopEnd; j-- {
					if byteAbsDiff(g.avgLuma, array[j].avgLuma) < uint8(minDiff*256.0) && (g.maxLuma > uint8((1.0-minDiff)*256.0) || array[j].minLuma < g.maxLuma+uint8(minDiff*256.0)) && (array[j].maxLuma > uint8((1.0-minDiff)*256.0) || g.minLuma < array[j].maxLuma+uint8(minDiff*256.0)) {
						diffTemp := gridDiffAlt(array[j], g, uint8(256.0*minDiff))
						if diffTemp < uint32(minDiff*256.0)*uint32(g.w)*uint32(g.h) {
							minDiff = float64(diffTemp) / 256.0
							minDiffC = j
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
		if 0 != w && 0 != h {
			g := Grid{w: w, h: h}
			g.array = make([][]uint8, w)
			var x uint8
			for x = 0; x < w; x++ {
				g.array[x] = make([]uint8, h)
				lSum := uint8(0)
				/*A simple attempt to copy the proper number of
				bytes from the file to the grid doesn't always
				work for some reason. This loop drags the program
				kicking and screaming to avoid copying byte-by
				-byte at this layer.*/
				for lSum < h {
					handle := make([]uint8, h-lSum)
					l, err := br.Read(handle)
					if err != nil {
						fmt.Println(err)
						return nil, err
					}
					copy(g.array[x][lSum:], handle[:l])
					lSum += uint8(l)
				}
			}
			g.resetLuma()
			array[i] = g
		} else {
			panic("Empty grid found while reading from file")
		}
	}
	sort.Slice(array, func(i, j int) bool { return lessGrid(array[i], array[j]) })
	return array, nil
}

/*Write the grid array to a file.*/
func writeToFile(array []Grid, fName string) error {
	byte_array := []byte("")
	/*Write the size of the array as a little-endian byte array.*/
	for i := 0; 6 > i; i++ {
		c := uint8((len(array) >> (8 * i)) % 256)
		byte_array = append(byte_array, byte(c))
	}
	/*Write the dimensions of each grid, followed by its pixels*/
	for i := 0; i < len(array); i++ {
		if 0 == array[i].w || 0 == array[i].h {
			panic("Empty grid found while writing to file")
		}
		byte_array = append(byte_array, byte(array[i].w))
		byte_array = append(byte_array, byte(array[i].h))
		var j uint8
		var k uint8
		for j = 0; j < array[i].w; j++ {
			for k = 0; k < array[i].h; k++ {
				byte_array = append(byte_array, byte(array[i].array[j][k]))
			}
		}
	}
	return os.WriteFile(fName, byte_array, 0777)
}

/*Combine two arrays.*/
func combineArrays(array1 []Grid, array2 []Grid, margin float64, tNum uint32) []Grid {
	arrayNew := make([]Grid, len(array1)+len(array2))
	copy(arrayNew, array1)
	copy(arrayNew[len(array1):], array2)
	sort.Slice(arrayNew, func(i, j int) bool { return lessGrid(arrayNew[i], arrayNew[j]) })
	start = time.Now().UnixNano()
	arrayNew = removeRedundantGrids(arrayNew, margin, tNum)
	arrayLen := len(arrayNew)
	for i := 0; i < arrayLen; i++ {
		if 0 == arrayNew[i].w && 0 == arrayNew[i].h {
			panic("Empty grid produced when combining arrays.")
		}
	}
	return arrayNew
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
		if nil != err {
			log.Fatal(err)
			return nil, err
		}
		return pngImg, err
	}
	img, format, err := image.Decode(f)
	if nil != err {
		fmt.Println("Decoding error: ", err.Error())
		return nil, err
	}
	fmt.Println(format)
	return img, nil
}

/*Convert an image to monocrhome and store it in an integer array*/
func convertToGrayscale(img image.Image, w int, h int) [][]uint8 {
	mono := make([][]uint8, w)
	/*Simply drop in the grayscale values for an image that is
	already monochrome.*/
	if strings.HasSuffix(strings.ToLower(reflect.TypeOf(img).String()), "gray") {
		for x := 0; x < w; x++ {
			mono[x] = make([]uint8, h)
			for y := 0; y < h; y++ {
				l, _, _, _ := img.At(x, y).RGBA()
				mono[x][y] = uint8(l >> 8)
			}
		}
	} else {
		/*Use basic color math to generate grayscale values*/
		for x := 0; x < w; x++ {
			mono[x] = make([]uint8, h)
			for y := 0; y < h; y++ {
				r, g, b, _ := img.At(x, y).RGBA()
				r >>= 8
				g >>= 8
				b >>= 8
				mono[x][y] = grayscale(uint8(r), uint8(g), uint8(b))
			}
		}
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
	/*This process is automatically called in the main method, whatever befall,
	so this statement is for if the intent never was to perform a luma trace
	on a color image.*/
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
				solve a blotching problem.*/
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
	rand.New(rand.NewSource(time.Now().UnixNano()))
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
	args := os.Args
	/*The following for loop creates arrays correspdonding to each of the
	above arguments.*/
	for i := 1; i < len(args); i++ {
		if "-k" == args[i] {
			j := i + 1
			for j < len(args) && 45 != args[j][0] {
				kArray = append(kArray, args[j])
				j++
			}
			i = j - 1
		} else if "-o" == args[i] {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				oArray = append(oArray, args[j])
				j++
			}
			i = j - 1
		} else if "-i" == args[i] {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				iArray = append(iArray, args[j])
				j++
			}
			i = j - 1
		} else if "-l" == args[i] {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				lArray = append(lArray, args[j])
				j++
			}
			i = j - 1
		} else if "-y" == args[i] {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				yArray = append(yArray, args[j])
				j++
			}
			i = j - 1
		} else if "-h" == args[i] {
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
			fmt.Println("The original purpose of this program was to make digitally-created images appear hand-drawn. However, it can be used for texturing of any kind.")
			return
		} else if "-t" == args[i] {
			j := i + 1
			for j < len(args) && args[j][0] != 45 {
				tArray = append(tArray, args[j])
				j++
			}
			i = j - 1
		}
	}
	/*These handle discoordinate arguments and arguments with an incorrect number of
	parameters.*/
	if len(kArray) == 0 && len(oArray) == 0 {
		if len(lArray) == 0 && len(iArray) == 0 && len(yArray) == 0 {
			fmt.Println("See list of options with -h.")
		} else {
			fmt.Println("Insufficient arguments, please specify either an output image using -o or an output dataset using -k")
		}
		return
	}
	if len(kArray) > 0 && 0 == len(iArray) && 0 == len(lArray) {
		fmt.Println("Output dataset specified without specifying input image using -i or input dataset using -l")
		return
	}
	if len(oArray) > 0 && 0 == len(yArray) && (0 == len(lArray) || 0 == len(iArray)) {
		fmt.Println("Output image specified without base image specified by -y or input image specified with -i or input dataset specified with -l")
		return
	}
	if len(oArray) > 1 {
		fmt.Printf("Please specify an output image file or a range with %c%c%cd, with X being the number of leading zeroes.\n", '%', '0', 'X')
		return
	}
	if len(yArray) > 0 && 0 == len(lArray) && 0 == len(iArray) {
		fmt.Println("Base image specified without input image specified with -i or input dataset specified with -l")
		return
	}
	if len(yArray) > 0 && 0 == len(oArray) {
		fmt.Println("Base image specified without output image specified with -o")
		return
	}
	if len(kArray) > 1 {
		fmt.Println("Too many dataset outputs specified. Please specify EXACTLY ONE output dataset.")
		return
	}
	if 2 == len(lArray) {
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
	}
	/*This handles inputting one or more file containing a grid array.*/
	tNum := uint32(1)
	if 1 == len(tArray) {
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
		arrayLen := len(array)
		for i := 0; i < arrayLen; i++ {
			for 0 == array[i].w || 0 == array[i].h {
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
				arrayLen = len(arrayTemp)
				for i := 0; i < arrayLen; i++ {
					for 0 == arrayTemp[i].w || 0 == arrayTemp[i].h {
						arrayTemp = append(arrayTemp[:i], arrayTemp[i+1:]...)
						arrayLen--
					}
				}
				array = combineArrays(array, arrayTemp, margin, tNum)
				fmt.Printf("%v\n", len(array))
			}

		}
	}
	/*This handles inputting one or more images for the purposes of creating grid arrays.*/
	if len(iArray) > 0 {
		minIn, errMin := strconv.ParseUint(iArray[len(iArray)-3], 10, 8)
		maxIn, errMax := strconv.ParseUint(iArray[len(iArray)-2], 10, 8)
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
		array = make([]Grid, 0)
		for i := 0; i < len(iArray)-3; i++ {
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
			t := generateTree(0, uint32(w), 0, uint32(h), uint8(minIn), uint8(maxIn))
			/*In order to make things simpler and to handle a divere set of colorspaces,
			an array of unsigned 8-bit integers holding the information from the image
			in black and white is used to create the grid.*/
			mono := convertToGrayscale(img, w, h)
			pix = 0
			start = time.Now().UnixNano()
			arraySize = 0
			tLeafCount := t.leafNum
			arraySub := make([]Grid, tLeafCount)
			arraySub = gridsFromTree(mono, t, arraySub, margin, w, h)
			arrayTemp := make([]Grid, len(arraySub)+len(array))
			copy(arrayTemp, arraySub)
			copy(arrayTemp[len(arraySub):], array)
			array = arrayTemp
		}
		sort.Slice(array, func(i, j int) bool { return lessGrid(array[i], array[j]) })
		start = time.Now().UnixNano()
		fmt.Println("Removing redundant grids")
		array = removeRedundantGrids(array, margin, tNum)
		end := time.Now().UnixNano()
		timeTotal := end - startTemp
		printTime(timeTotal)
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
		if 3 == len(yArray) {
			for i := 0; i < cifLength; i++ {
				if strings.HasSuffix(strings.ToUpper(oArray[0]), fmt.Sprintf("%s%s", ".", commonImageFormats[i])) {
					foundExt += 1
					break
				}
			}
			outputFileNames[0] = oArray[0]
			if 0 == foundExt {
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
			if nil == matches || 0 == len(matches) {
				foundExt = 0
				for i := 0; i < cifLength; i++ {
					if strings.HasSuffix(strings.ToUpper(oArray[0]), fmt.Sprintf("%s%s", ".", commonImageFormats[i])) {
						foundExt += 1
						break
					}
				}
				if 0 != foundExt {
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
				if 1 != len(splitOnDot) {
					for i := 0; foundExt != 0 && i < cifLength; i++ {
						foundExt *= int8(strings.Compare(strings.ToUpper(splitOnDot[len(splitOnDot)-1]), commonImageFormats[i]))
					}
				}
			}
			/*The output filename does not include a (common) file extension.*/
			if 0 != foundExt {
				foundExt = int8((1 << cifLength) - 1)
				for i := 0; i < len(yArray)-2; i++ {
					for j := 0; j < cifLength; j++ {
						foundExt &= int8(^((1 - absInt(strings.Compare(strings.ToUpper(yArray[i][len(yArray[i])-len(commonImageFormats[j])-1:]), fmt.Sprint(".", commonImageFormats[j])))) << j))
					}
				}
				k := kern(uint8(foundExt))
				if k < cifLength {
					/*The input filenames collectively include one distinct (common) file extension.*/
					if 1 == cifLength-k {
						extCursor := int8(0)
						for 1 == 1&(foundExt>>extCursor) {
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
				if 0 == strings.Compare(outputFileNames[i], yArray[j]) {
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
			mono := convertToGrayscale(img, w, h)
			monoNew := make([][]uint8, w)
			for i := 0; i < w; i++ {
				monoNew[i] = make([]uint8, h)
				for j := 0; j < h; j++ {
					monoNew[i][j] = 0
				}
			}
			pix = 0

			fmt.Println("Performing luma trace on " + yArray[i])
			start = time.Now().UnixNano()
			startTemp := start
			monoNew = lumaTrace(mono, monoNew, array, t, uint32(tNum))
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
	if 1 == len(kArray) {
		writeToFile(array, kArray[0])
	}
}

