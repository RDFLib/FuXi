FuXi \
--closure \
--output="n3" \
--ns=test=http://xdors.net/demo# \
--dlp \
--input-format="n3" \
--method=bfp \
--rules=./test1.formulae.n3 \
--why="SELECT ?x ?y WHERE { ?x test:has_child ?y  }" \
--why="SELECT ?x ?y WHERE { ?x test:has_sibling ?y  }" \
./test1.ontology.n3 \
./test1.individuals.n3 
