FuXi \
--firstAnswer \
--debug \
--method=bfp \
--safety=loose \
--output=conflict \
--normalize \
--ns='ub=http://www.lehigh.edu/~zhp2/2004/0401/univ-bench.owl#' \
--ns='ex=http://www.Department0.University0.edu/' \
--why="ASK { ?class a ub:Course  }" \
--dlp \
--ontology=http://www.lehigh.edu/%7Ezhp2/2004/0401/univ-bench.owl \
http://swat.cse.lehigh.edu/projects/lubm/University0_0.owl
