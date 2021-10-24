exec >> jobList.txt
for fn in ${HOME}/zdd/Gitrepo/compilationRealizabilityWitnesses/2QBF2016/2QBF/subtraction*.qdimacs
do
    b="$(basename ${fn} .qdimacs)"
    export filename=$b
    sbatch run_zdd.slurm
    echo $filename
    echo " "
done
