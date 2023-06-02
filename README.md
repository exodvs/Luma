#Luma

##A program for texturing images based on a set of different images

- [Installation]
- [Usage]
- [Conext, motivation, and development]
- [Credits]

## Installation
Download and run using your favorite Go tools.

##Usage
-i	Create a dataset to be used as the texture of output images, using one or more pictures, followed by the desired minimum and maximum dimensions of fragments
	of an image and the margin above which all images need to be different by.
	go run ./Luma.go -i image.png 4 10 0.05
	The above command takes the data from image.png and requires data fragments to be at least 5% different from each other in order to remain.
-l	Import an existing set that can also be produced by this program. Can also be used for multiple datasets, but this requires a margin similar to the margin in -i
	after all filenames.
	go run ./Luma.go -l set1.txt (set2.txt 0.05)
-y	Trace over an image, and texture it to look like the data captured by -i or -l. Requires minimum and maximum dimensions like -i, but no margin.
-o	Specify the output of a trace made by -y. Can be a sequence of image files, but it needs %0Xd, where X is the number of leading zeroes.
-k	Save dataset created by the program to a file.

##Context, motivation, and development
I am a hobbyist animator and I prefer the texture and look of animation from the golden and television ages of animation, lasting roughly from the beginning of prerecorded dialogue in the medium in the late 1920s to the peak of Bakshi's career and Bluth's defection from Disney around 1982. Various other animators around my age and older intnetionally use various tricks with varying success to imitate the look and feel of older animation despite primarily using digital tools.
I tried various noise filters, line-squiggle effects, coloration tricks, and even texturing animation on top of scans of blank sheets of paper, none of which succeeded in making my animation look hand-made. Whatever qualities older animation has is something that NLEs, animation software, and special FX software is not meant to directly imitate. Therefore, I took it upon myself to "teach" a computer what traditional animation looks like.
Since the look is achieved by small irregularities in the linework and filmgrain, it seemed that the solution was to show the computer various examples of how these details should appear. The primary purpose of this program is to take one or more image (in its intended case, stillframes from hand-drawn animation) and break it apart into fragments, and to take another image (in its intended case, frames of digitally-produced animation) and break it into fragments as well, and find the closest fragments in the first set, transplanting them into an alternate version of the second image. In theory, the result will appear as old-fashioned frames of animation.

The first step of this process involved decided what kind of data structures would be required. I found the easisest way to randomly split apart an image such that each and every one of its pixels would be included in a strict rectangle (i.e. no l-shaped regions) was a tree with x and y coordinates, and a minimum and maximum size. As for the image fragments themselves, the grid structure was a very early idea, and appeared in its early development mostly remebling its current form, with the array and the dimensions.
At first, I simply developed code until I could get an image subdivided correctly by the tree, and use this tree to create grids. The next step was to sort the grids. Early on, I decided that the primary means of sorting grids would be by dimensions. However, searches would still take a long time, such that it would take several minutes to process one image. In order to reduce search size, I added a margin variable to various methods. The user is allowed to decided how different each grid has to be from other grids produced by the program. This helped somewhat, but images still took several minues to process, and had a mottled, blotched look.
I tried adding median brightness to the search criteria as a way to reduce search time, both in the process of eliminated redundant grids and finding the right replacement grid. This was later changed to average brightness due to taking considerably less time (as it does not require a sorting process for every grid and images too far away to possibly be redundant are easier to determine).
Early development of this program took place in Python, as that could be developed easily remotely over a command line (unlike, say, Java which is generally developed in Eclipse or another graphical IDE) and handled various image formates using built-in methods (unlike C). While the program was still being tested, I was in the process of learning Go. Unrelated to the development of Luma, I performed a prime-number test in C, Go, and Python, and discovered that for such a basic task, Python took several seconds while neither of the other programs exceeded one second. I started porting Luma (then called Image Analysis) to Go. It took considerable to figure out PNG support, but I eventually was able to make a functioning version of the program that took considerably less time.
The process for searching for possible redundant arrays and for possible matches were two bottlenecks even in Go, and blotching still plagued the output images in tests. An earlier version of the code simply found the most similar grid from a base image as the grid was created. I had to rewrite the program so that an image's grids were stored, sorted, and then compared to the existing array. This involved the creation of a map that alaso stored coordinates, and the most immediate advantage was that instead of doing a binary search over the entire array each time, the program would have endpoints of the array that encompassed all other grids of the same dimension to the one under examination. Once no more grids with those same dimensions were being examined, the program would look elsewhere, stay in the new section as long as it needed to, and so on. My tests involved grids between 4 and 10 pixels in either axis, inclusive, meaning that only 49 binary searches were needed instead of the tens of thousands needed previously.
During previous testing, the program's method for adding new girds to the set of hand-drawn data and the method used to eliminate redundant grids involved a grid-by-grid addition to a list (in Python) or slice (in Go). This itself was taking considerable time, so I rewrote the program to simply add each grid as it came, sort then, and then eliminate before adding to an array of a predefined size. To determine which would stay and which would be discarded, the program uses an array of unsigned integers that are altered through bitwise operations. The set bits are used to indicate those which will remain.
Finally, the blotching problem was solved mostly by requiring the corners of two grids be similar in brightness before eliminating one of them.
It currently takes less than a second to trace over a 1080p image, against an array of over 400000 grids. Actually producing this array takes considerable time, but it is not something that can be easily sped up. There is simply no way to save most of several dozen images that takes less than several seconds.

##Credits
This program was written entirely by Jake Raymond.

##License
This program is available under the GNU General Public License v3.0
