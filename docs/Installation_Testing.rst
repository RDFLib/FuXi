==============================================================================
Installation Testing -  
==============================================================================

Introduction
===============================

These instructions try to provide enough information
so a curious programmer, previously unfamiliar with python, can kick the tires
on FuXi without a lot of pain

Fuxi is currently developed and supported under python 2.5.1.
`FuXi </p/fuxi/wiki/FuXi>`_ requires setuptools (ez_setup) to install.
The scripts that follow create a 2.5 version of
`FuXi </p/fuxi/wiki/FuXi>`_ for a system that has a higher release level
of python (than 2.5) installed. If 2.5 is your current python version,
you can substitute ``python`` for ``python2.5`` and ``easy_install`` for
``easy_install-2.5`` in these examples.

The simplest way to install `FuXi </p/fuxi/wiki/FuXi>`_ is with
easy_install:

::

    wget http://peak.telecommunity.com/dist/ez_setup.py
    python2.5 ez_setup.py
    easy_install-2.5 fuxi
    Fuxi

Details
=====================

To build `FuXi </p/fuxi/wiki/FuXi>`_ from scratch from sources requires
the mercurial and subversion source code control systems both be
installed. The build also requires the libraries ``pyparsing`` and
``layercake`` (a
`custom <http://code.google.com/p/python-dlp/wiki/LayerCakePythonDivergence>`_
fork of rdflib) for RDF processing. To install and build sources:

::

      * This script requires that ez_setup, mercurial (hg) and subversion (svn) are installed.
      * Sources will be installed in the working directory.
    sudo easy_install pyparsing
    svn export http://python-dlp.googlecode.com/svn/trunk/layercake-python  # create local copy of layercake
    cd layercake-python
    sudo python2.5 setup.py build
    sudo python2.5 setup.py install
    cd ..
    hg clone https://fuxi.googlecode.com/hg/ fuxi   # clone FuXi from repository using Mercurial
    cd fuxi
    sudo python2.5 setup.py build
    sudo python2.5 setup.py install

Note at runtime `FuXi </p/fuxi/wiki/FuXi>`_ can also optionally import
and utilize:

-  `Boost <http://www.generic-programming.org/~dgregor/bgl-python/>`_
   Graph Library - Python Bindings are used to enable
   `FuXi </p/fuxi/wiki/FuXi>`_'s Network instances to be exported to a
   Graphviz DOT file and rendered to any image format. This provides a
   nice visual feedback to the discrimination network built to a
   ruleset.

-  `nose <http://somethingaboutorange.com/mrl/projects/nose/0.11.2/>`_ -
   a testing utility used to enable cleaner execution of the test suite,
   with better summary statistics.

For more information about the `FuXi </p/fuxi/wiki/FuXi>`_ project and
current release see

-  Release notes (under discussion)

-  The `DOAP <http://usefulinc.com/doap/>`_ file:
   `/trunk/fuxi/FuXi.rdf <https://fuxi.googlecode.com/hg/FuXi.rdf>`_

Testing and Maintenance
=====================================================

To verify `FuXi </p/fuxi/wiki/FuXi>`_ installation and functioning, run
some tests. A good place to start is with the standalone unit tests
found under ``fuxi/test``. These can be executed individually at the
command line.

The module ``testOWL.py`` requires some manual setup to provide useful
results. Refer to ``OWL-TESTS.txt`` in ``/fuxi/test/OWL`` for
instructions to download the current W3C OWL test battery. Unzip that
file and move its folders directly beneath the ``/fuxi/test/OWL``
folder. At this point you can invoke the battery by executing testOWL at
the command line. By default testOWL runs the battery using the ``gms``
inference strategy, but ``sld`` and ``bfp`` can alternatively be
specified using the ``--strategy`` flag. Besides standalone unit tests,
`FuXi </p/fuxi/wiki/FuXi>`_ embeds unit tests and/or doctests in most
production modules. These can typically be invoked at the command line
(as "test mains").

You also can invoke all tests--standalone and embedded, unittest and
doctest--by running ``/fuxi/test/suite.py``. The ``--variants`` switch
with this command causes testOWL to run with each of the strategies gms,
sld and bfp .

`FuXi </p/fuxi/wiki/FuXi>`_ may be released with some tests in error.
Consult the release notes for further information. Also, refer to the
`issues
list <http://code.google.com/p/fuxi/issues/list?thanks=12&ts=1277984968>`_
for outstanding maintenance and enhancement requests.

