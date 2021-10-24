#!/bin/bash
#SBATCH --partition=commons
#SBATCH --export=ALL
#SBATCH --job-name=sgrk
#SBATCH --cpus-per-task=1
#SBATCH --ntasks=1
#SBATCH --nodes=1 --exclusive
#SBATCH --constraint=ivybridge
#SBATCH --time=01:00:00
#SBATCH --mem=32g
#SBATCH --output=out/sgrk-%j.out
#SBATCH --error=err/sgrk-%j.err

sgrk=${HOME}/separation-grk/sgrk
benchmarks=${HOME}/separation-grk/benchmarks
results=${HOME}/cav21/results/average

timefile=${results}/${filename}.sgrk.time
outfile=${results}/${filename}.sgrk.out

specfile=${benchmarks}/${filename}.sgrk

>&2 echo "Running ${filename} using SGrk..."

(/usr/bin/time -f "%e %S %U" ${sgrk} ${specfile} > ${outfile}) 2> ${timefile}
