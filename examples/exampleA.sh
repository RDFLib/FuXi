FuXi -d \
--safety=loose \
--strictness=defaultDerived \
--idb=owl:sameAs \
--method=bfp \
--hybrid \
--why="ASK { ex:subject1 owl:sameAs ex:subject2 }" \
--ns=ex=http://www.w3.org/2002/03owlt/InverseFunctionalProperty/premises001#  \
--pDSemantics \
--builtinTemplates=http://fuxi.googlecode.com/hg/RuleBuiltinSPARQLTemplates.n3 \
--dlp \
http://www.w3.org/2002/03owlt/InverseFunctionalProperty/premises001.rdf

