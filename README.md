# Explicit Construction of the Maximal Subgroups of the Monster

This notebook complements the paper of the same name by Heiko Dietrich,
Melissa Lee, Anthony Pisani, and Tomasz Popiel. It contains
the computational components of the proofs, including generators
for the 45 (out of 46) maximal subgroups of $\MM$ constructed,
along with extensive annotations. Computations are performed using
the [`mmgroup`](https://github.com/Martin-Seysen/mmgroup) package, for which
a brief guide is provided in the notebook [`subgroups.ipynb`](subgroups.ipynb).
See also the [official documentation](https://mmgroup.readthedocs.io).

Several auxiliary functions and variables, mostly imported
from the accompanying file [`helpers.py`](helpers.py), are used repeatedly
throughout the notebook. The code for all proofs is otherwise independent:
after running an initialising cell, one can begin execution
at any subsection. Logical interdependence is indicated
by appropriate references in the textual annotations, with recurring variables
defined in each subsection where they appear.

Sample GAP code for verifying some of the claims made in the paper
is included in the file [`extras.g`](extras.g).
