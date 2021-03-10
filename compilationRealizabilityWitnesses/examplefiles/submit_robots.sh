for i in {1..10}
do
        export filename=cleaning_robots_${i}
        sbatch run_sgrk.slurm
done
