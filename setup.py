import ez_setup
ez_setup.use_setuptools()
from setuptools  import setup
setup(name="FuXi",
      version="1.0",
      description="An OWL / N3-based in-memory, logic reasoning system for RDF",
      author="Chime Ogbuji",
      author_email="chimezie@gmail.com",
      package_dir = {
        'FuXi': 'lib',
      },
      packages=[
        "FuXi",
        "FuXi.Rete",
        "FuXi.DLP",
        "FuXi.Horn",
        "FuXi.Syntax",
        "FuXi.SPARQL",
      ],
      install_requires = ['rdflib<3a',],#'telescope'],
      license = "BSD",
      keywords = "python logic owl rdf dlp n3 rule reasoner",
      url = "http://code.google.com/p/python-dlp/wiki/FuXi",
      entry_points = {
       'console_scripts': [
           'FuXi = FuXi.Rete.CommandLine:main',
        ],
      },
      zip_safe=False
)
