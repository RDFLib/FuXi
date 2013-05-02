from rdflib import Graph, RDF, URIRef
from FuXi.Syntax.InfixOWL import OWL_NS, Class

# local source:
# galenGraph = Graph().parse(
#     os.path.join(os.path.dirname(__file__), 'GALEN-CABG-Segment.owl'))

# remote source:
galenGraph = Graph().parse(
    location="http://python-dlp.googlecode.com/" + \
             "svn/trunk/InfixOWL/GALEN-CABG-Segment.owl",
    format="xml")

graph = galenGraph

with open('GALEN-CABG-Segment.asc', 'w') as fp:
    for c in graph.subjects(predicate=RDF.type, object=OWL_NS.Class):
        if isinstance(c, URIRef):
            fp.write(Class(c, graph=graph).__repr__(True) + "\n\n")

print("Done")
