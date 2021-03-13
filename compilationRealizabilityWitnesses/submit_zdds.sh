for fn in ${HOME}/zdd/Gitrepo/compilationRealizabilityWitnesses/2QBF2016/2QBF/*k_ph*.qdimacs
do
    b="$(basename ${fn} .qdimacs)"
    export filename=$b
    sbatch run_zdd.slurm
done
