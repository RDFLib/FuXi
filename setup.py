#!/usr/bin/env python
# -*- coding: utf-8 -*-
import sys
import re
try:
    import multiprocessing  # atexit exception
except:
    pass


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

config = dict(
    name="FuXi",
    version="1.4",
    description="An OWL / N3-based in-memory, logic reasoning system for RDF",
    author="Chime Ogbuji",
    author_email="chimezie@gmail.com",
    maintainer="RDFLib Team",
    maintainer_email="rdflib-dev@google.com",
    platforms=["any"],
    classifiers=[
        "Programming Language :: Python",
        "Programming Language :: Python :: 2",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 2.5",
        "Programming Language :: Python :: 2.6",
        "Programming Language :: Python :: 2.7",
        "Programming Language :: Python :: 3.2",
        "Programming Language :: Python :: 3.3",
        "License :: OSI Approved :: BSD License",
        "Topic :: Software Development :: Libraries :: Python Modules",
        "Operating System :: OS Independent",
        "Natural Language :: English",
       ],
    package_dir={
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
    install_requires=['rdflib>2'],
    license="Apache",
    keywords="python logic owl rdf dlp n3 rule reasoner",
    test_suite='nose.collector',
    url="https://github.com/RDFLib/FuXi",
    entry_points={
        'console_scripts': [
           'FuXi = FuXi.Rete.CommandLine:main',
        ],
    },
    zip_safe=False
)

kwargs = {}
if sys.version_info[0] >= 3:
    from setuptools import setup
    assert setup
    kwargs['use_2to3'] = True
    kwargs['src_root'] = setup_python3()
else:
    try:
        from setuptools import setup
        assert setup
    except ImportError:
        from distutils.core import setup

setup(**config)
