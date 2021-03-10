#!/bin/bash

#SBATCH --nodes=1 --exclusive
#SBATCH --export=ALL
#SBATCH --partition=commons
#SBATCH --job-name=compilReal
#SBATCH --cpus-per-task=1
#SBATCH --constraint=ivybridge
#SBATCH --ntasks=1
#SBATCH --time=08:00:00
#SBATCH --mail-user=yl182@rice.edu
#SBATCH --mail-type=ALL
#SBATCH --output=out/compilReal-%j.out
#SBATCH --error=err/compilReal-%j.err

compilReal=${HOME}/zdd/Gitrepo/compilationRealizabilityWitnesses/
benchmarks=${HOME}/zdd/Gitrepo/compilationRealizabilityWitnesses/2QBF2016/2QBF
results=${HOME}/zdd/Gitrepo/compilationRealizabilityWitnesses/NOTSresults

timefile=${results}/${filename}.compilReal.time
outfile=${results}/${filename}.compilReal.out

specfile=${benchmarks}/${filename}.compilReal

>&2 echo "Running ${filename} using compilReal..."

(/usr/bin/time -f "%e %S %U" ${compilReal} ${specfile} > ${outfile}) 2> ${timefile}