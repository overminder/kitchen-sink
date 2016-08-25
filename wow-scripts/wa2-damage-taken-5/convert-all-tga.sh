for f in $(find res -name "*.tga"); do
  echo "Converting $f -> $f.png"
  convert $f $f.png
done
