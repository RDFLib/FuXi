#!/usr/bin/env python
# -*- coding: utf-8 -*-
import sys
import re

def setup_python3():
    # Taken from "distribute" setup.py
    from distutils.filelist import FileList
    from distutils import dir_util, file_util, util, log
    from os.path import join
  
    tmp_src = join("build", "src")
    log.set_verbosity(1)
    fl = FileList()
    for line in open("MANIFEST.in"):
        if not line.strip():
            continue
        fl.process_template_line(line)
    dir_util.create_tree(tmp_src, fl.files)
    outfiles_2to3 = []
    for f in fl.files:
        outf, copied = file_util.copy_file(f, join(tmp_src, f), update=1)
        if copied and outf.endswith(".py"):
            outfiles_2to3.append(outf)
  
    util.run_2to3(outfiles_2to3)
  
    # arrange setup to use the copy
    sys.path.insert(0, tmp_src)

    return tmp_src

# Find version. We have to do this because we can't import it in Python 3 until
# its been automatically converted in the setup process.
def find_version(filename):
    _version_re = re.compile(r'__version__ = "(.*)"')
    for line in open(filename):
        version_match = _version_re.match(line)
        if version_match:
            return version_match.group(1)

__version__ = find_version('lib/__init__.py')

import ez_setup
ez_setup.use_setuptools()
from setuptools  import setup

config=dict(
    name="FuXi",
    version="1.3",
    description="An OWL / N3-based in-memory, logic reasoning system for RDF",
    author="Chime Ogbuji",
    author_email="chimezie@gmail.com",
    platforms = ["any"],
    classifiers = ["Programming Language :: Python",
                   "Programming Language :: Python :: 2",
                   "Programming Language :: Python :: 3",
                   "Programming Language :: Python :: 2.5",
                   "Programming Language :: Python :: 2.6",
                   "Programming Language :: Python :: 2.7",
                   "Programming Language :: Python :: 3.2",
                   "License :: OSI Approved :: BSD License",
                   "Topic :: Software Development :: Libraries :: Python Modules",
                   "Operating System :: OS Independent",
                   "Natural Language :: English",
                   ],
    package_dir = {
        'FuXi': 'lib',
    },
    packages=[
        "FuXi",
        "FuXi.LP",
        "FuXi.SPARQL",
        "FuXi.Rete",
        "FuXi.DLP",
        "FuXi.Horn",
        "FuXi.Syntax",
    ],
    install_requires = ['rdflib',],#'telescope'],
    license = "Apache",
    keywords = "python logic owl rdf dlp n3 rule reasoner",
    url = "http://code.google.com/p/python-dlp/wiki/FuXi",
    entry_points = {
        'console_scripts': [
           'FuXi = FuXi.Rete.CommandLine:main',
        ],
    },
    zip_safe=False
)

if sys.version_info[0] >= 3:
    config.update({'use_2to3': True})
    config.update({'src_root': setup_python3()})
else:
    config.update({'test_suite' : "nose.collector"})

setup(**config)

