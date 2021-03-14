#!/bin/bash

#SBATCH --nodes=1 --exclusive
#SBATCH --export=ALL
#SBATCH --partition=commons
#SBATCH --job-name=compilReal
#SBATCH --cpus-per-task=1
#SBATCH --constraint=ivybridge
#SBATCH --ntasks=1
#SBATCH --time=24:00:00
#SBATCH --mem=64g
#SBATCH --mail-user=yl182@rice.edu
#SBATCH --mail-type=ALL
#SBATCH --output=out/compilReal-%j.out
#SBATCH --error=err/compilReal-%j.err
compilReal=${HOME}/zdd/Gitrepo/compilationRealizabilityWitnesses/cudd0
benchmarks=${HOME}/zdd/Gitrepo/compilationRealizabilityWitnesses/2QBF2016/2QBF
results=${HOME}/zdd/Gitrepo/compilationRealizabilityWitnesses/NOTSresults

outfile=${results}/${filename}.out

specfile=${benchmarks}/${filename}.qdimacs
echo "This is the outfile for ${filename}"



${compilReal} ${specfile} > ${outfile}

