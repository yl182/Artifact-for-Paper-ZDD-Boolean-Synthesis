for fn in $./2QBF2016/2QBF/*.qdimacs
do
    b="$(basename ${fn})"
    echo $b
    ./cudd0 $fn 0 0
    echo " "
done
