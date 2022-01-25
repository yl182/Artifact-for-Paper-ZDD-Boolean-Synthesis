# New Version

An updated version of this artifact is permanently publicly available at https://zenodo.org/record/5898695#.YfBUKv7MJPY.

# ZDD Boolean Synthesis

This is a ZDD-based synthesis tool as the artifact for research paper ``ZDD Boolean Synthesis`` for TACAS submission 2022. This tool is used in the paper compared to RSynth in previous work.

## installation and compilation

Please first extract the tarball "ZDDSynthesisTarball.tar.gz" and follow steps below.

This project requires C++ of version at least 11, and includes a modified ``CUDD`` package in cudd-release. It also includes the ``QMRes`` functions from previous work by Pan and Vardi under QMRes directory.

The source code are placed under the top layer of directories.

To compile, just run ``make`` under ZDDBooleanSynthesis directory.

To remove .dot files after running, run ``make clean``. This command does not eliminate previous running results in ``resultsSynthesis.csv``. The first line labels the names of the columns.

The ``Makefile`` also includes sample scripts for usage listed below.

## Run on a single benchmark
To run on a single benchmark, simply use ```./cudd0 <benchmark-filepath> <whether-to-enable-dotfile-outputs> <whether-to-enable-details-in-output>```, where:

``<benchmark-filepath>`` is the path of the single benchmark to execute on.
If ``<whether-to-enable-dotfile-outputs>`` is set to 1, some intermediate ZDDs constructed through the end-to-end process can output as .dot files, and the ZDDs are not saved if this flag is replaced by other values.
If ``<whether-to-enable-details-in-output>`` is 1, details are written to standard out. Other values to this flag sets to default mode with simple details. It is recommended to be 0.

Experimental results are reported to separate files ``resultsSynthesis.csv`` and ``resultsSynthesis.txt``, independent of values to the two values above.

The default mode in .sh files provided for executing on multiple benchmarks assumes ```0 0``` to the two commandline arguments above.

For example, ``` ./cudd0 2QBF2016/2QBF/tree-exa10-10.qdimacs 1 1``` runs the compiled code on benchmark tree-exa10-10 from QBFEVAL2016 dataset, where a set of intermediate ZDDs are saved as .dot files, 
which can be then converted to figures by ``dot <ZDD-name.dot> -Tpng -o <ZDD-name.png>``, or ``dot <ZDD-name.dot> -Tpdf -o <ZDD-name.pdf>``.

As another example, ``` ./cudd0 2QBF2016/2QBF/tree-exa10-10.qdimacs 0 0``` runs on the same benchmark file, with concise standard output and no dot files produced, but the result will also be reported in ``resultsSynthesis.csv`` and ``resultsSynthesis.txt``.
## Run all benchmarks in a specific family
To run a benchmark in a specific family, use the .sh scripts provided, or the following in ZDDBooleanSynthesis directory:
```
for fn in $2QBF2016/2QBF/*<keyword-for-the-family>*.qdimacs
do
    b="$(basename ${fn})"
    ./cudd0 $fn 0 0
done
```

```./run_mutex_family.sh``` sequentially starts running the ZDD Synthesis tool on all MutexP family benchmarks.
```./run_qshifter_family.sh``` runs on all QShifter family benchmarks.
```./run_stmt_family.sh``` runs sequentially on all Fix Point Detection family benchmarks, similarly.
## Run on all benchmarks in the dataset
Use ``./run_evalAll.sh`` to include all .qdimacs benchmarks from QBFEVAL2016. Note we generated scalable benchmarks qshifter_9 and qshifter_10, and they can be excluded from QBFEVAL benchmarks.

## How to run on additional benchmarks
To run on a new additional benchmark, simple use ```./cudd0 <benchmark-filepath> <whether-to-enable-dotfile-outputs> <whether-to-enable-details-in-output>```, where ``<benchmark-filepath>`` must be a full path of the new benchmark.

## Results collection
  The results are reported in resultsSynthesis.csv, where the first row labels what the columns represent.
## Publicity of repository
We can make the code public on Zenodo after acceptance or further refinement.

## Revision Notes and Comments
The instructions above generate resultsSynthesis.csv, whose content covers the realizability time, compilation, and witness-construction time and space. The synthesis time needs to be sumed up in the csv file.

For end-to-end running, the range of running time: the shortest time is 0.017s, and the longest running time is 15540s. If time is limitted, you can run the smaller families include Tree, MutexP, and QShifter 3-5.

There are executable files to run each benchmark families separately, e.g., run_stmt_family.sh and run_qshifter_family.sh. The instructions are above.

The ```DataReferenceTables``` folder includes the original data we collected for your reference to the figures in the paper, one for each respectively. For example, ```PercentageEndToEnd.csv``` includes the data we use for plotting the Figure.2 which illustrates the percentage of files finished on end-to-end experiments within certain time scopes. The plots in the paper are generated in these csv files using the data in them.

Note that every time the running time and space can be various, but the data you see between same set of benchmarks should show the same relative patterns as those in ```DataReferenceTables/```. 

Figure.1 in paper comes from ```DataReferenceTables/CompilationTime.csv```, using filenames as the X-axis and compilation time in milliseconds as the Y-axis; Fig. 2 in paper comes from ```DataReferenceTables/PercentageRealizability.csv```, using the log-scale time increased by 10x as the X-axis and percentage of total number of finished tests as Y-axis; Fig. 3 in paper comes from ```DataReferenceTables/PercentageEndToEnd.csv```, similarly to Fig. 2 but considers the sum of compilation time, realizability time and witness-construction time ; Fig. 4 in paper comes from ```DataReferenceTables/Scalable.csv```, using files as X-axis and the passed time as primary Y-axis for items on time comparison, while number of nodes as the secondary Y-axis for space.

The RSynth tool we compare ZSynth with is documented by RSynth authors here: bitbucket.org/lucas-mt/RSynth. For your convenience, the RSynth data are also included in correspondence columns of data attached in ```DataReferenceTables```.

The ```QMRes``` directory contains libraries for a few of our functions. It is not a tool we compare the performance of ZSynth with.

A set of small test files reside in ```testFiles```.

The tool is for experiments on academic uses to observe the time and space performance of ZSynth, not a mature industrial product. The format of generated ZDDs are .dot. The ZDDs for the original formula and the witnesses (indexed with variable indices) are output as ``.dot`` files. To check for correctness, simply use ```dot ZDD.dot -Tpng -o ZDD.png``` or ```dot ZDD.dot -Tpdf -o ZDD.pdf```, etc., to view the diagrams in image formats, with relevant command-line tools installed.

CPU details for NOTS, where we ran the experiments on, are here: https://kb.rice.edu/page.php?id=108237.
