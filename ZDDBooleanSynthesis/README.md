# ZDD Boolean Synthesis

This is a ZDD-based synthesis tool as the artifact for research paper ``ZDD Boolean Synthesis`` for TACAS submission 2022. This tool is used in the paper compared to RSynth in previous work.

## installation and compilation

This project requires C++ of version at least 11, and includes a modified ``CUDD`` package in cudd-release. It also includes the ``QMRes`` functions from previous work by Pan and Vardi under QMRes directory.

The source code are placed under the top layer of directories.

To compile, just run ``make`` under ZDDBooleanSynthesis directory.

To remove .dot files after running, run ``make clean``.

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
  The results are reported in resultsSynthesis.txt and resultsSynthesis.csv, where the first row labels what the columns represent.
