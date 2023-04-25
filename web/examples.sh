#!/bin/bash

files=(src/evaluation/*.ml)

for file in "${files[@]}"; do
  contents="$(sed 's/"/\&quot;/g' < "$file")"
  transformed_contents="<option value=\"$contents\">$file</option>"
  output+="$transformed_contents"
done

MORE="$output" envsubst < "$1" > index1.html
cp index1.html "$2"

