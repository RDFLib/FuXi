echo a party ====================================== 
FuXi --input-format="n3" --ns=test=http://xdors.net/demo# --dlp \
  --method=bfp --rules=./test2.formulae.n3  \
  --why="SELECT ?x WHERE { ?x a test:party  }" \
  ./test2.ontology.n3 ./test2.individuals.n3 
echo has parent ====================================== 
FuXi --input-format="n3" --ns=test=http://xdors.net/demo# --dlp \
  --method=bfp --rules=./test2.formulae.n3  \
  --why="SELECT ?x ?y WHERE { ?x test:has_parent ?y  }" \
  ./test2.ontology.n3 ./test2.individuals.n3 
echo has sibling ====================================== 
FuXi --input-format="n3" --ns=test=http://xdors.net/demo# --dlp \
  --method=bfp --rules=./test2.formulae.n3  \
  --why="SELECT ?x ?y WHERE { ?x test:has_sibling ?y  }" \
  ./test2.ontology.n3 ./test2.individuals.n3 
