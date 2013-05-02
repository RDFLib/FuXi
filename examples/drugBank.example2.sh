FuXi \
  --output=rif \
  --safety=loose \
  --strictness=loose \
  --ddlGraph=./drugBankDDL.n3 \
  --method=bfp \
  --output=n3 \
  --why="SELECT ?label { ?drug a drugbank:InfluenzaDrug; rdfs:label ?label }" \
  --debug \
  --ontology=./drugBankOnt.n3 \
  --ontologyFormat=n3 \
  --builtinTemplates=http://fuxi.googlecode.com/hg/RuleBuiltinSPARQLTemplates.n3 \
  --sparqlEndpoint \
  --dlp http://www4.wiwiss.fu-berlin.de/drugbank/sparql

