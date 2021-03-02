for file in *.dot
do
	b="$(basename ${file} .dot)"
	#echo $b
	echo "Converting $b.dot to $b.png..."
	dot $b.dot -Tpng -o $b.png
	dot $b.dot -Tpdf -o $b.pdf
done
