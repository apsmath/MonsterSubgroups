"""
$
\def \udot {\cdot}
\def \textup {\text}
\newcommand{\CO}{\textup{Co}_1}
\newcommand{\FI}{\textup{Fi}_{24}}
\newcommand{\SZ}{\textup{Suz}}
\newcommand{\HE}{\textup{He}}
\newcommand{\HN}{\textup{HN}}
\newcommand{\Th}{\textup{Th}}
\newcommand{\QStr}{2^{1+24}}
\newcommand{\BB}{\mathbb{B}}
\newcommand{\MM}{\mathbb{M}}
\newcommand{\QQ}{\mathbf{Q}}
\newcommand{\GG}{\mathbf{G}}
\newcommand{\J}[1]{\textup{J}_{#1}}
\newcommand{\MT}[1]{\textup{M}_{#1}}
\newcommand{\dih}[1]{\textup{D}_{#1}}
\newcommand{\sdih}[1]{\textup{SD}_{#1}}
\newcommand{\psl}[2]{\textup{PSL}_{#1} \left( #2 \right)}
\newcommand{\pgl}[2]{\textup{PGL}_{#1} \left( #2 \right)}
\newcommand{\ling}[2]{\textup{GL}_{#1} \left( #2 \right)}
\newcommand{\lins}[2]{\textup{SL}_{#1} \left( #2 \right)}
\newcommand{\unt}[2]{\textup{U}_{#1} \left( #2 \right)}
\newcommand{\orth}[3]{\textup{O}_{#2}^{#1} \left( #3 \right)}
\newcommand{\lie}[3]{\textup{#1}_{#2} \left( #3 \right)}
\newcommand{\alt}[1]{\textup{A}_{#1}}
\newcommand{\sym}[1]{\textup{S}_{#1}}
\newcommand{\symp}[2]{\textup{S}_{#1} \left( #2 \right)}
\newcommand{\aut}[1]{\textup{Aut} \left( #1 \right)}
\newcommand{\cm}[1]{C_\MM \left( #1 \right)}
\newcommand{\nm}[1]{N_\MM \left( #1 \right)}
\newcommand{\cma}[1]{C_\MM \left( \langle #1 \rangle \right)}
\newcommand{\nma}[1]{N_\MM \left( \langle #1 \rangle \right)}
$
# Explicit Construction of the Maximal Subgroups of the Monster

<a id="intro"></a>
This notebook complements the paper of the same name by Heiko Dietrich,
Melissa Lee, Anthony Pisani, and Tomasz Popiel. It contains
the computational components of the proofs, including generators
for the 45 (out of 46) maximal subgroups of $\MM$ constructed,
along with extensive annotations. Computations are performed using
the [`mmgroup`](https://github.com/Martin-Seysen/mmgroup) package, for which
a [brief guide](#mmgroup) is provided below. See also
the [official documentation](https://mmgroup.readthedocs.io).

Several auxiliary functions and variables, mostly imported
from the accompanying file `helpers.py`, are used repeatedly
throughout this document. The code for all proofs is otherwise independent:
after running an [initialising cell](#begin), one can begin execution
at any subsection. Logical interdependence is indicated
by appropriate references in the textual annotations, with recurring variables
defined in each subsection where they appear.

## Table of Contents <a id="toc"></a>

Theorems and lemmas are numbered in accordance with the paper.


<table border="1">
 <thead><th colspan="3">

  Introduction

 </th></thead><tbody>
  <tr><td>
 
   [Introduction](#intro)

  </td><td></td><td></td></tr><tr><td>

   [Table of Contents](#toc)

  </td><td></td><td></td></tr><tr><td>

   [A Brief Introduction to `mmgroup`](#mmgroup)

  </td><td></td><td></td></tr>
 </tbody><thead><th colspan="3">

  Odd-local subgroups

 </th></thead><tbody>
  <tr><td>

   [Theorem 2.5](#norm3A)

  </td><td>

   $3 \udot \FI$

  </td><td>

   Proof adapted from Dietrich, Lee, and Popiel

  </td></tr>
  <tr><td>

   [Theorem 2.6](#norm3B)

  </td><td>

   $3^{1+12} \udot 2 \udot \SZ{:}2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.7](#norm3C)

  </td><td>

   $\sym{3} \times \Th$

  </td><td>

   Proof adapted from Dietrich, Lee, and Popiel

  </td></tr>
  <tr><td>

   [Theorem 2.8](#norm3A2)

  </td><td>

   $\left( 3^2{:}2 \times \orth+{8}{3} \right) \udot \sym{4}$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.9](#norm3B2)

  </td><td>

   $3^{2+5+10}{:}\left( \MT{11} \times 2.\sym{4} \right)$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.10](#norm3B3)

  </td><td>

   $3^{3+2+6+6}{:}\left( \psl{3}{3} \times \sdih{16} \right)$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.11](#norm3Ark)

  </td><td>

   $3^8 \udot \orth-{8}{3}.2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.12](#norm5A)

  </td><td>

   $\left( \dih{10} \times \HN \right) \udot 2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.13](#norm5B)

  </td><td>

   $5^{1+6}{:}2 \udot \J2{:}4$

  </td><td>

   Generators adapted from Dietrich, Lee, and Popiel

  </td></tr>
  <tr><td>

   [Theorem 2.14](#norm5A2)

  </td><td>

   $\left( 5^2{:}4 \udot 2^2 \times \unt{3}{5} \right){:}\sym{3}$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.15](#norm5B2)

  </td><td>

   $5^{2+2+4}{:}\left( \sym{3} \times \ling{2}{5} \right)$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.16](#norm5B3)

  </td><td>

   $5^{3+3} \udot \left( 2 \times \psl{3}{5} \right)$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.17](#norm5B4)

  </td><td>

   $5^4{:}\left( 3 \times 2 \udot \psl{2}{25} \right){:}2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.18](#norm7A)

  </td><td>

   $\left( 7{:}3 \times \HE \right){:}2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.19](#norm7B)

  </td><td>

   $7^{1+4}{:}\left( 3 \times 2.\sym{7} \right)$

  </td><td>

   Generators adapted from Dietrich, Lee, and Popiel

  </td></tr>
  <tr><td>

   [Theorem 2.20](#norm7A2)

  </td><td>

   $\left( 7^2{:} \left( 3 \times 2.\alt{4} \right) \times \psl{2}{7} \right){:}2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.21](#norm7B2)

  </td><td>

   $7^{2+1+2}{:}\ling{2}{7}$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.22](#norm7B2p)

  </td><td>

   $7^2{:}\lins{2}{7}$

  </td><td>

   Proof adapted from Pisani and Popiel

  </td></tr>
  <tr><td>

   [Theorem 2.23](#norm11_2)

  </td><td>

   $11^2{:}\left( 5 {\times} 2.\alt{5} \right)$

  </td><td>

   Proof adapted from Pisani and Popiel

  </td></tr>
  <tr><td>

   [Theorem 2.24](#norm13A)

  </td><td>

   $\left( 13{:}6 \times \psl{3}{3} \right) \udot 2$

  </td><td>

   Proof for index 2 subgroup adapted from Dietrich, Lee, and Popiel

  </td></tr>
  <tr><td>

   [Theorem 2.25](#norm13B)

  </td><td>

   $13^{1+2}{:}\left( 3 \times 4.\sym{4} \right)$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.26](#norm13B2)

  </td><td>

   $13^2{:}\lins{2}{13}{:}4$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 2.27](#norm41)

  </td><td>

   $41{:}40$

  </td><td>
  </td></tr>
  <tr><td>-</td><td>

   $59{:}29$

  </td><td>

   No instance currently known

  </td></tr>
 </tbody><thead><th colspan="3">

  2-local subgroups

 </th></thead><tbody>
  <tr><td>

   [2A centraliser](#norm2A)

  </td><td>

   $2 \udot \BB$

  </td><td>

   Proof adapted from Dietrich, Lee, and Popiel

  </td></tr>
  <tr><td>

   [2B centraliser](#norm2B)

  </td><td>

   $\QStr \udot \CO$

  </td><td>

   Proof adapted from Dietrich, Lee, and Popiel

  </td></tr>
  <tr><td>

   [Theorem 3.5](#norm2A2)

  </td><td>

   $2^2 \udot {}^2 \lie{E}{6}{2} {:} \sym{3}$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 3.6](#norm2B2)

  </td><td>

   $2^{2+11+22} \udot \left( \MT{24} \times \sym{3} \right)$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 3.7](#norm2B3)

  </td><td>

   $2^{3+6+12+18} \udot \left( \psl{3}{2} \times 3.\sym{6} \right)$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 3.8](#norm2B5)

  </td><td>

   $2^{5+10+20} \udot \left( \sym{3} \times \psl{5}{2} \right)$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 3.9](#normArk)

  </td><td>

   $2^{10+16} \udot \orth+{10}{2}$

  </td><td>
  </td></tr>
 </tbody><thead><th colspan="3">

  $\alt{5}$ in the Monster <a id="lemma"></a>

 </th></thead><tbody>
  <tr><td>

   [Lemma 4.1](#lemma)

  </td><td>

   $\alt{5}$s

  </td><td>

   Many cases adapted from Dietrich, Lee, and Popiel

  </td></tr>
 </tbody><thead><th colspan="3">

  Projective Linear Groups

 </th></thead><tbody>
  <tr><td>

   [Theorem 5.1](#psl2_71)

  </td><td>

   $\psl{2}{71}$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 5.2](#psl2_41)

  </td><td>

   $\psl{2}{41}$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 5.3](#pgl2_29)

  </td><td>

   $\pgl{2}{29}$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 5.4](#pgl2_19)

  </td><td>

   $\pgl{2}{19}$

  </td><td>

   Proof adapted from Pisani and Popiel

  </td></tr>
  <tr><td>

   [Theorem 5.5](#pgl2_13)

  </td><td>

   $\pgl{2}{13}$

  </td><td>

   Proof adapted from Dietrich, Lee, and Popiel

  </td></tr>
  <tr><td>

   [Theorem 5.6](#psl2_59)

  </td><td>

   $\psl{2}{59}$

  </td><td>

   Non-existence proof

  </td></tr>
 </tbody><thead><th colspan="3">

  Non-Local Subgroups

 </th></thead><tbody>
  <tr><td>

   [Theorem 6.2](#normAAA)

  </td><td>

   $\left( \alt{5} \times \alt{12} \right){:}2$

  </td><td>

   Proof for index 2 subgroup adapted from Dietrich, Lee, and Popiel

  </td></tr>
  <tr><td>

   [Theorem 6.3](#normA6_3)

  </td><td>

   $\left( \alt{6} \times \alt{6} \times \alt{6} \right).\left( 2 \times \sym{4} \right)$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 6.4](#normACA)

  </td><td>

   $\left( \alt{5} \times \unt{3}{8}{:}3 \right){:}2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 6.5](#normL7)

  </td><td>

   $\left( \psl{3}{2} \times \symp{4}{4}{:}2 \right) \udot 2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 6.6](#normL11)

  </td><td>

   $\left( \psl{2}{11} \times \MT{12} \right){:}2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 6.7](#normA7)

  </td><td>

   $\left( \alt{7} \times \left( \alt{5} \times \alt{5} \right){:}2^2 \right){:}2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 6.8](#normA6)

  </td><td>

   $\MT{11} \times \alt{6} \udot 2^2$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 6.9](#normS5_3)

  </td><td>

   $\left( \sym{5} \times \sym{5} \times \sym{5} \right){:}\sym{3}$

  </td><td>
  </td></tr>
  <tr><td>

   [Theorem 6.10](#normL11_2)

  </td><td>

   $\left( \psl{2}{11} \times \psl{2}{11} \right){:}4$

  </td><td>

   Proof adapted from Pisani and Popiel

  </td></tr>
  <tr><td>

   [Theorem 6.11](#unt3_4_4)

  </td><td>

   $\unt{3}{4}{:}4$

  </td><td>

   Proof adapted from Dietrich, Lee, and Popiel

  </td></tr>
</table>

## A Brief Introduction to `mmgroup` <a id="mmgroup"></a>

For the construction of elements and computations in $\MM$, we employ
the Python package [mmgroup](https://github.com/Martin-Seysen/mmgroup).
The following table adapted from Dietrich et al. (2023) describes
some important functions provided by this package; the object `g`
represents $g \in \MM$. Basic group operations in $\MM$ are performed
with the expected Python operators, although it is notable that `1/g`
is equivalent to `g**-1`.

<table border="1">
<tr><td>

  `MM('r','M')`

</td><td>

  produces a random element in $\MM$

</td></tr>
<tr><td>

  `MM('r','G_x0')`

</td><td>
  produces a random element in $\GG$

</td></tr>
<tr><td>

  `MM('r','N_0')`

</td><td>

  produces a random element in $\mathbf{N}_0 = \nma{z, z^{\tau}}$,

</td></tr>
<tr><td>

  `g.as_int()`

</td><td>

  returns an integer uniquely representing $g$

</td></tr>
<tr><td>

  `g.in_G_x0()`

</td><td>

  decides whether $g \in \GG$

</td></tr>
<tr><td>

  `g.in_Q_x0()`

</td><td>

  decides whether $g$ lies in the normal subgroup $\QQ$ of $\GG$

</td></tr>
<tr><td>

  `g.conjugate_involution()`

</td><td>

  determines involution $g$'s class;
  returns $h \in \MM$ with $g^h \in \left\{ y, z \right\}$

</td></tr>
<tr><td>

  `g.chi_G_x0()`

</td><td>

  for $g \in \GG$ (only), returns
  $\left( \chi_\MM \left( g \right), \chi_{299} \left( g \right),
  \chi_{24} \left( g \right), \chi_{4096} \left( g \right) \right)$.
  Here, $\chi_\MM$ denotes the complex character of the unique
  irreducible 196883-dimensional representation of $\MM$;
  the associated module restricts to $\GG \cong 2^{1+24} \udot \textup{Co}_1$
  as $196883 = 299 \oplus 98280 \oplus (24 \otimes 4096)$,
  with the characters $\chi_{299}$, $\chi_{24}$, and $\chi_{4096}$ corresponding
  to the 299, the 24, and the 4096.

</td></tr>
<tr><td>

  `g.as_Co1_bitmatrix()`

</td><td>

  for $g \in \GG$ (only), returns $m \in \ling{24}{2}$
  representing $\QQ g \in \GG / \QQ$

</td></tr>
</table>
"""
"""
Load some utilities and preliminary data. <a id="begin"></a>
"""

from helpers import MM, dim_q, size_image, e, z, check_singular, check_normalise, as_int, to_co1, comm, test_m11, map_to_vectors, test_xsl, test_pgl, check_lemma_2_2


# Generators for various subgroups A5
A5_dict = {
    "AAA": (MM("M<y_3dch*x_57fh*d_11ch*p_164842291*l_1*p_2640000*l_1*p_935210>"), MM("M<y_321h*x_361h*d_0a6dh*p_47182817*l_1*p_960*l_1*p_2112*l_1*p_2356800>")),
    "BAA": (MM("M<y_7afh*x_181fh*d_5bch*p_33460650*l_2*p_5115840>"), MM("M<y_237h*x_47ah*d_0c49h*p_31024125*l_1*p_466560*l_1*p_211776>")),
    "BBA": (MM("M<y_19bh*x_179h*d_0dd3h*p_2301167*l_2*p_1457280*l_1*p_464855*t_2*l_1*p_1394880*l_1*p_1457616*l_1*t_1*l_1*p_1499520*l_1*p_10671585*l_2*t_2*l_2*p_2787840*l_2*p_22753393*l_1*t_1*l_2*p_5760*l_1*t_1*l_2*p_2597760*l_1*p_85372339>"), MM("M<y_4d3h*x_7e9h*d_0b6ch*p_39136178*l_2*p_2344320*l_2*p_523428*t_1*l_1*p_2640000*l_1*p_22750595*l_1*t_1*l_1*p_2999040*l_1*p_33441186*l_1*t_2*l_1*p_1457280*l_2*p_7681*t_1*l_2*p_2830080*l_2*p_42676071*t_1*l_1*p_2999040*l_1*p_106706501*l_1*p_11594880*t_2*l_1*p_2640000*l_1*p_11222811>")),
    "ACA": (MM("M<y_106h*x_804h*d_50ah*p_10221120>"), MM("M<y_556h*x_1a7fh*d_0e26h*p_95605306*l_2*p_1985280*l_1*p_661019>")),
    "BCA": (MM("M<y_4f6h*x_1f98h*d_0b7h*p_67615847*l_1*p_2999040*l_1*p_86264262*l_2*p_11172480>"), MM("M<y_17h*x_2cdh*d_540h*p_21413172*l_1*p_1499520*l_2*p_64122837*l_2*p_1920>")),
    "BCB": (MM("M<y_4f6h*x_1f98h*d_0b7h*p_67615847*l_1*p_2999040*l_1*p_86264262*l_2*p_11172480>"), MM("M<y_4e1h*x_19cbh*d_9c8h*p_19643307*l_1*p_2999040*l_1*p_64003504*l_2*p_1478400>")),
    "B": (MM("M<y_64h*x_56dh*d_325h*p_219161657*l_2*p_17318400*l_1*p_11552640*t_1*l_2*p_80319360*l_2*p_131324208*l_1*t_1*l_1*p_70561920*l_1*p_209827200*l_1*t_2*l_2*p_6673920*l_1*p_63909120>"), MM("M<y_437h*x_0f53h*d_3ah*p_148262400*l_2*p_1985280*l_1*p_32978359*t_1*l_1*p_2027520*l_1*p_11688432*l_1*t_1*l_2*p_1394880*l_1*p_10665936*l_2*p_2416320*t_1*l_1*p_2027520*l_1*p_470471*t_2*l_2*p_2830080*l_2*p_106661290*t_1*l_2*p_2597760*l_1*p_43613421*t_2*l_2*p_2830080*l_2*p_96456578>")),
    "T": (MM("M<y_1a4h*x_9aah*d_6h*p_183850438*l_2*p_2787840*l_2*p_22811953*t_1*l_1*p_1499520*l_2*p_32977413*l_2*t_2*l_1*p_1499520*l_2*p_1866474*l_2*t_2*l_2*p_2830080*l_2*p_11177514*t_1*l_2*p_1900800*l_2*p_18279*t_2*l_2*p_2787840*l_2*p_507110*t_2*l_2*p_2386560*l_2*p_42757857>"), MM("M<y_501h*x_0b20h*d_5a0h*p_55017756*l_1*p_466560*l_1*p_32993856*t_2*l_1*p_2999040*l_1*p_1480810*l_1*t_1*l_1*p_44837760*t_1*l_2*p_2956800*l_1*p_96035088*t_2*l_2*p_2956800*l_1*p_53352355>"))
}

# The following elements, commented out, are used to obtain
# the type AAA and BAA, respectively, from Dietrich, Lee, and Popiel's.
# The type BCB and B are used unmodified, while the type T is not used at all.
conjugator_AAA = MM("M<y_1abh*x_0dd0h*d_5d8h*p_15333704*l_2*p_1457280*l_1*p_33395058*t_2*l_2*p_2597760*l_1*p_10780224*t_1*l_2*p_1985280*l_1*p_10781120*t_2*l_2*p_2386560*l_2*p_43195600*t_2*l_1*p_1457280*l_2*p_180898>")
conjugator_BAA = MM("M<y_475h*x_0d42h*d_188h*p_211601633*l_2*p_1900800*l_2*p_53361063*t_1*l_2*p_2386560*l_2*p_33392032*t_1*l_1*p_22080*l_2*p_929664*t_1*l_1*p_203174400*l_2*t_1>")

"""
# Odd-local subgroups

## $3 \udot \FI$ <a id="norm3A"></a>
The following proof is adapted from Dietrich, Lee, and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

*Standard* generators are given by
"""

g3 = MM("M<y_5f6h*x_0fbeh*d_2ebh*p_193227272*l_2*p_2830080*l_2*p_32067203*t_2*l_2*p_2344320*l_2*p_12596663*l_1*t_2*l_2*p_1415040*l_1*p_21817200*l_2*t_2*l_2*p_1943040*l_2*p_22351232*l_2*t_1*l_1*p_2027520*l_1*p_13443*t_2*l_1*p_1457280*l_2*p_53938>")
h3 = MM("M<y_743h*x_11f4h*d_391h*p_92316215*l_1*p_2999040*l_1*p_467894*t_1*l_1*p_2999040*l_1*p_26931*l_1*t_2*l_2*p_1900800*l_2*p_33465249*l_1*t_1*l_2*p_2830080*l_2*p_85326162*t_2*l_1*p_1457280*l_2*p_129106*t_2*l_1*p_1499520*l_2*p_1485571*l_1*t_1*l_2*p_2597760*l_1*p_53391808*t_2*l_1*p_1499520*l_2*p_42667429>")
L_N = (g3, h3)

"""
This is the normaliser of a 3A element in the Monster. We claim this particular instance normalises
"""

x3 = MM("M<y_3dbh*x_14c9h*d_1c6h*p_238425007*l_2*p_1985280*l_1*p_11174636*l_2>")
L_E = [x3]

"""
Firstly, verify $x_3$ belongs to the correct conjugacy class using $\chi_\MM$:
"""

x3.order() # 3
x3.in_G_x0() # True
x3.chi_G_x0()[0] # 782

"""
With that settled, show the claimed generators belong to the normaliser of $x_3$.
"""

check_normalise(L_E, L_N) # True

"""
As for showing the entire normaliser is generated,
begin by verifying that $\langle g_3, h_3 \rangle$
contains a representative of each coset in $\nma{x_3} / \langle x_3 \rangle \cong \FI$.
To this end, observe that only maximal subgroup of $\FI$ with order divisible
by both 29 and 70 is $\text{F}_3^+$, which does not contain elements of order 70.
It therefore suffices to exhibit elements with these orders, both coprime to 3, in $3 \udot \FI$.
"""

(g3*h3).order() # 29
((g3*h3)**5*h3).order() # 70

"""
It then only remains to verify that $x_3 \in \langle g_3, h_3 \rangle$:
"""

(g3*h3*g3*h3**3*g3*h3**5)**28 == x3 # True

"""
We further claim that the following elements $g_3$ and $h_3$ are standard generators
for $\nma{x_3} \cong 3 \udot \FI$. This means that, as well as being generators,

1. $g_3$ projects to class 2C in the quotient $\nma{x_3} / \langle x_3 \rangle \cong \FI = \text{Fi}_{24}'{:}2$, 
2. $h_3$ projects to class 8D in $\FI$, and
3. $\left| g_3 h_3 \right| = 29$.

The character table of $\FI$ in GAP indicates that all elements of order $46$ power to class 2C, and
that all elements of order $40$ power to class 8D; furthermore, both orders are coprime to 3, guaranteeing
that elements of these orders in $3 \udot \FI$ project to elements of the same orders in the quotient.
The following elements normalise $\langle x_3 \rangle$, have order $46$ and $40$, respectively, and power to $g_3$ and $h_3$,
respectively, so it follows that conditions 1 and 2 hold.
"""

g46 = MM("M<y_5feh*x_1f1h*d_292h*p_192994065*l_2*p_60360960*l_1*p_230672640*t_1*l_2*p_1985280*l_1*p_12135864*l_1*t_2*l_1*p_1457280*l_2*p_36672*l_1*t_2*l_2*p_2597760*l_1*p_63996822*t_1*l_2*p_1943040*l_2*p_11604637*l_2*t_1*l_2*p_1943040*l_2*p_63998817*t_2*l_2*p_2956800*l_1*p_42706001>")
g40 = MM("M<y_57fh*x_1d3h*d_603h*p_39537390*l_2*p_2344320*l_2*p_53820870*t_2*l_1*p_1457280*l_2*p_464944*l_2*t_1*l_2*p_1985280*l_1*p_32547596*l_2*t_2*l_2*p_1943040*l_2*p_43600722*t_1*l_2*p_1985280*l_1*p_42731872*t_2*l_2*p_1457280*l_1*p_71216*t_2*l_2*p_2956800*l_1*p_106698940>")

check_normalise([x3], (g40, g46)) # True
g40.order(), g46.order() # (40, 46)
g46**23 == g3 # True
g40**5 == h3 # True

"""
Finally, condition 3 was verified in exhibiting the element $g_3 h_3$ of order 29 above.
"""

"""
## $3^{1+12} \udot 2 \udot \SZ{:}2$ <a id="norm3B"></a>
Generators are given by
"""

g3b = MM("M<y_7f7h*x_1b7ah*d_1b2h*p_186721955*l_1*p_1457280*l_2*p_11725977*l_2*t_1*l_1*p_2999040*l_1*p_1415386*l_1*t_2*l_2*p_2597760*l_1*p_22314818*l_2*t_1*l_2*p_1457280*l_1*p_9639*t_1*l_2*p_1943040*l_2*p_42789700*t_1*l_2*p_2597760*l_1*p_85413716*l_1*p_2344320*t_2*l_1*p_467520*l_1*p_2788128*l_1>")
h3b = MM("M<y_13bh*x_1c48h*d_4d9h*p_102050909*l_1*p_80762880*l_1*p_151282608*l_1*t_2*l_1*p_7560960*l_2*p_12439680*l_2*t_1*l_2*p_2597760*l_1*p_22356004*l_2*t_1*l_2*p_2787840*l_2*p_13464*t_2*l_1*p_47498880*l_2*p_42620352*t_2*l_2*p_1985280*l_1*p_64124776*t_2*l_2*p_1985280*l_1*p_42708878*t_2*l_2*p_2956800*l_1*p_64046790>")
L_N = (g3b, h3b)

"""
This is the normaliser of a 3B element in the Monster. We claim this particular instance normalises
"""

x3b = MM("M<y_5d4h*x_17efh*d_0f7eh*p_183231946*l_2*p_2787840*l_2*p_22759172>")
L_E = [x3b]

"""
Firstly, verify $x_{3b}$ belongs to the correct conjugacy class using $\chi_\MM$:
"""

x3b.order() # 3
x3b.in_G_x0() # True
x3b.chi_G_x0()[0] # 53

"""
With that settled, show the claimed generators belong to the normaliser of $x_{3b}$.
"""

check_normalise(L_E, L_N) # True

"""
As for showing the entire normaliser is generated, begin by proving
that all cosets of the normal subgroup $3^{1+12}.2$, forming the factor group
$\SZ.2$, are generated.
"""

g3b.order() # 56
h3b.order() # 66

"""
The greatest common factor of 56 (respectively, 66) and $3^{1+12} \cdot 2$
is 2 (respectively, 6), so that some power thereof must project to an element
of order 28 (respectively, 11) in $\SZ.2$. However, data in the GAP
character table library shows that the only maximal subgroup of $\SZ.2$
with order divisible by both 28 and 11 is $\SZ$, which does not
contain elements of order 28: hence, the entire factor group $\SZ.2$
is generated.

Now, since $\SZ.2$ contains no elements of order 56 and $\text{gcd} \left( 56, 3^{1+12} \cdot 2 \right) = 2$,
the 28^th power of $g_{3b}$ must lie in the normal subgroup $3^{1+12}.2$ of the 3B normaliser.
Having order 2, it (and any of its conjugates) will lie in the outer coset of $3^{1+12}$.
A representative of this coset is therefore present, while an element of the $3^{1+12}$ --- itself
a normal subgroup of $\nma{x_{3b}}$ --- can be generated by multiplying $g_{3b}^{28}$
with a conjugate. The elements in $\left\{ x_{3b}, y_{3b}, \ell \right\}$, `gs`, and `hs`
below thus belong to the $3^{1+12}$.
"""

y3b = MM("M<y_4ech*x_0aeeh*d_83bh*p_240916280*l_2*p_2597760*l_1*p_169605*t_2*l_1*p_2027520*l_1*p_22750595*t_2*l_1*p_2640000*l_1*p_178009*t_2*l_1*p_960*l_2*p_53815392*t_2*l_1*p_1415040*l_1*p_2256*l_2*p_76800*t_2*l_2*p_8004480*l_2*p_63909120>")
gs = (
    MM("M<y_58eh*x_8fh*d_2c9h*p_76285619*l_2*p_1457280*l_1*p_32103884*t_2*l_1*p_960*l_2*p_10665888*l_2*p_3763200*t_1*l_1*p_2027520*l_1*p_13020096*l_2*t_1*l_2*p_2956800*l_1*p_53349541*t_2*l_2*p_1415040*l_1*p_466800*l_2*p_3465600*t_1*l_2*p_2386560*l_2*p_42717489*t_2*l_2*p_2956800*l_1*p_85370418>"),
    MM("M<y_662h*x_17f8h*d_0ff0h*p_233651083*l_1*p_543360*t_1*l_1*p_2027520*l_1*p_47239*t_2*l_2*p_1457280*l_1*p_578263*t_1*l_1*p_15100800*t_2*l_2*p_2597760*l_1*p_21426569*t_1*l_2*p_2597760*l_1*p_64078688*t_1*l_1*p_1499520*l_1*p_85328065>"),
    MM("M<y_778h*x_0a7dh*d_0b20h*p_61290019*l_2*p_234220800*t_2*l_2*p_1943040*l_2*p_2352323*l_1*t_2*l_1*p_1858560*l_2*p_23280*l_1*p_2411520*t_2*l_1*p_3823680*t_1*l_1*p_68787840*l_1*p_108704736*t_1*l_2*p_2956800*l_1*p_53814185*t_1*l_2*p_59917440*l_1*p_127776096>"),
    MM("M<y_91h*x_550h*d_8f8h*p_131387342*l_2*p_1900800*l_2*p_21865336*l_2*t_1*l_1*p_1415040*l_1*p_23328*l_2*p_1520640*t_2*l_2*p_1943040*l_2*p_2414887*l_1*t_2*l_1*p_1099200*t_2*l_2*p_2830080*l_2*p_42796362*t_2*l_2*p_1943040*l_2*p_85816867*t_2*l_2*p_2956800*l_1*p_53381152>"),
    MM("M<y_36dh*x_0f60h*d_312h*p_128810854*l_1*p_2640000*l_1*p_21865335*t_1*l_2*p_2830080*l_2*p_21370*l_2*t_2*l_2*p_1985280*l_1*p_32504018*l_2*t_2*l_2*p_1943040*l_2*p_12176258*l_2*t_1*l_2*p_1900800*l_2*p_5763*t_2*l_2*p_2830080*l_2*p_42671248>")
)
hs = (
    MM("M<y_0abh*x_13d0h*d_0f66h*p_197048161*l_1*p_1858560*l_1*p_465936*l_2*p_510720*t_1*l_2*p_24000*l_2*p_488160*t_1*l_2*p_2386560*l_2*p_64036498*t_2*l_2*p_2787840*l_2*p_2800905*l_2*t_2*l_2*p_2787840*l_2*p_11554*t_2*l_1*p_2640000*l_1*p_13458>"),
    MM("M<y_119h*x_75bh*d_8bbh*p_203279177*l_2*p_2830080*l_2*p_10671544*t_1*l_1*p_2027520*l_1*p_22307968*l_1*t_1*l_2*p_2956800*l_1*p_21888592*l_2*t_1*l_1*p_1499520*l_2*p_42677961*t_2*l_2*p_2830080*l_2*p_21336113*t_1*l_1*p_1457280*l_2*p_12994999*l_1*t_1*l_2*p_2830080*l_2*p_21345778>"),
    MM("M<y_1a3h*x_0b74h*d_0a38h*p_201631922*l_2*p_2344320*l_2*p_33013873*l_2*t_1*l_1*p_1499520*l_2*p_467786*l_1*t_2*l_2*p_1393920*l_2*p_3120*l_1*p_1206720*t_1*l_2*p_1900800*l_2*p_3104*t_2*l_2*p_1858560*l_1*p_10665888*l_1*p_699840*t_2*l_2*p_5641920*l_1*t_1*l_2*p_1900800*l_2*p_137698>"),
    MM("M<y_0f2h*x_1c21h*d_0e0fh*p_228919392*l_1*p_80319360*l_2*p_231116160*t_1*l_2*p_1900800*l_2*p_22774569*l_2*t_1*l_2*p_2787840*l_2*p_33013910*l_1*t_1*l_2*p_1943040*l_2*p_33460438*l_1*t_2*l_1*p_2027520*l_1*p_5761*t_2*l_2*p_2830080*l_2*p_42798259>"),
    MM("M<y_4b1h*x_1162h*d_3b3h*p_195698166*l_2*p_2956800*l_1*p_32978354*l_2*t_1*l_1*p_2640000*l_1*p_2859335*l_2*t_1*l_2*p_1900800*l_2*p_2388161*l_1*t_2*l_1*p_467520*l_1*p_85056*t_2*l_1*p_1499520*l_1*p_85820694*t_2*l_2*p_1943040*l_2*p_85367645*t_2*l_2*p_1943040*l_2*p_42729963>")
)

r = (g3b**28)*(g3b**28)**h3b
cnj1 = [g3b**4*(h3b*g3b)**2*g3b, g3b*h3b**3*g3b*h3b*g3b**3, g3b*h3b*g3b**2*h3b*(h3b*g3b)**2, (h3b*g3b)**2*g3b*(h3b*g3b)**2]
cnj2 = [h3b**2*g3b**4*h3b*g3b**3, g3b*h3b**3*g3b**2*h3b, h3b*g3b**6*h3b**2*g3b, g3b*h3b**2*g3b**3*h3b**2*g3b**2, h3b*g3b**2*h3b**2*g3b*h3b]

gs == (r**cnj1[2]*r**cnj2[0], r**cnj1[3], r**(cnj1[0]*h3b)/r**cnj2[0], r**(cnj1[2]*h3b), r**cnj2[0]) # True
hs == (r**cnj2[1], r**cnj2[2], r**cnj2[3]/r**cnj2[2], r**cnj2[4]*r**cnj2[2], (r**cnj2[1])**2*r**cnj2[3]*r) # True
x3b == (r**cnj1[0])**2*(r**cnj1[1])**2*gs[0]*gs[2]*gs[3]**2 # True
y3b == (r**cnj1[0])**2*gs[0]*gs[2]*gs[3]**2*gs[4]**2 # True
l = (r**(g3b**2)).reduce()

"""
They in fact satisfy all the conditions for Lemma 2.2
with $N = 3^{1+12}$ and $\sigma$ as defined below:
"""

σ = MM("M<y_46ch*x_19b9h*d_9f4h*p_43971768*l_1*p_2640000*l_1*p_11712608*l_2*t_1*l_2*p_2597760*l_1*p_11222741*t_1*l_2*p_1943040*l_2*p_11225569*t_2*l_2*p_2386560*l_2*p_10741665*t_1*l_2*p_1985280*l_1*p_86283414*l_1*p_10688640*t_2*l_2*p_1858560*l_1*p_3168*l_2*p_10436160>")
check_lemma_2_2(x3b, y3b, l, gs, hs, σ) # True

"""
We conclude that $x_{3b}$, $y_{3b}$, $\ell$, `gs`, and `hs` generate
$3^{1+12}$, and therefore that the entire subgroup $\nma{x_{3b}} \cong 3^{1+12} \udot 2 \udot \SZ{:}2$
lies in $\langle g_{3b}, h_{3b} \rangle$.
"""

"""
## $\sym{3} \times \Th$ <a id="norm3C"></a>
The following proof is adapted from Dietrich, Lee, and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

*Standard* generators are given by
"""

g3c = MM("M<y_170h*x_10bfh*d_809h*p_198739923*l_1*p_49716480*l_2*p_172571520*l_2*t_1*l_1*p_2640000*l_1*p_12575584*l_1*t_1*l_2*p_1858560*l_1*p_10666848*l_1*p_2093760*t_2*l_1*p_1499520*l_1*p_10804218*t_1*l_2*p_2956800*l_1*p_53436116*t_2*l_2*p_2386560*l_2*p_85412773*t_1*l_1*p_1499520*l_1*p_106661296>")
h3c = MM("M<y_0b5h*x_955h*d_2e1h*p_197852501*l_1*p_70561920*l_1*p_232890288*l_1*t_1*l_1*p_79875840*l_1*p_203617920*l_2*t_2*l_2*p_68344320*l_2*p_202730880*l_1*t_1*l_1*p_117575040*l_1*t_2*l_1*p_109148160*l_2>")
L_N = (g3c, h3c)

"""
These are `a*c3` and `b*c2` in the notation of Dietrich et al. The choice of elements there
is motivated by various considerations which do not concern us here; for more details, see
the original argument.

This subgroup is the normaliser of a 3C element in the Monster. We claim this particular instance normalises
"""

x3c = MM("M<y_4cdh*x_1274h*d_499h*p_8151915*l_2*p_1900800*l_2*p_43255347*t_2*l_2*p_2597760*l_1*p_479249*l_2*t_2*l_1*p_4654080*t_1*l_2*p_2956800*l_1*p_53436116*t_2*l_2*p_2386560*l_2*p_85412773*t_1*l_1*p_1499520*l_1*p_106661296>")
L_E = [x3c]

"""
Firstly, verify $x_{3c}$ belongs to the correct conjugacy class using $\chi_\MM$:
"""

x3c.order() # 3

# Conjugate x3c into G_x0 by sending an involution with which it commutes to z.
x3c_conj = (x3c**(g3c**3).conjugate_involution()[1]).reduce()
x3c_conj.in_G_x0() # True
x3c_conj.chi_G_x0()[0] # -1

"""
With that settled, show the claimed generators belong to the normaliser of $x_{3c}$.
"""

check_normalise(L_E, L_N) # True

"""
As for showing the entire normaliser is generated, begin by proving $g_{3c}$ and $h_{3c}$ generate each element of the factor $\text{Th}$.
We in fact prove that $a = g_{3c}^3$ and $b = h_{3c}^4$ do so:
it suffices to exhibit an element of order $19$ and an element order $31$ in $\langle a,b \rangle$,
because both orders are coprime to $6 = \left| \sym{3} \right|$ and no maximal subgroup of $\text{Th}$ contains
an element of order $31$ and an element of order $19$.
"""

a = g3c**3
b = h3c**4
(a*b).order() # 19
(a*b*a*b**2*a*b**2*a*b*a*b**2*a*b*a*b*a*b*a*b**2*a*b**2*a*b*a*b).order() # 31

"""
It remains to show that $x_2 = h_{3c}^3$ and $x_{3c} = g_{3c}^4$ satisfy
$\left| x_2 \right|=2$, $\left| x_3 \right|=3$, and $x_3^{x_2} = x_3^{-1}$,
so they generate the factor group isomorphic to $\sym{3}$.
"""

x2 = h3c**3
x3c == g3c**4 # True
x2.order() # 2
x3c**x2 == 1/x3c # True

"""
We further claim that $g_{3c}$ and $h_{3c}$ project to standard generators $a, b$
for $\text{Th}$. This means that, as well as being generators, they lie in the same
cosets of $\sym{3}$ as $a, b$ respectively and

1. $a$ has order $2$, 
2. $b$ lies in the $\text{Th}$-class 3A, 
3. $ab$ has order $19$.

It is easily verified that $a, b$ centralise $\langle x_2, x_{3c}$
and thus lie in $\text{Th}$, which they were shown to generate
(modulo the $\sym{3}$) above:
"""

# Obviously x3c = g3c**4 and x2 = h3c**3 commute with a = g3c**3 and b = h3c**4, respectively
x2*a == a*x2 # True
x3c*b == b*x3c # True

"""
Conditions 1 is also readily checked, and 3 was shown in exhibiting $ab$ as an element of order 19 above.
"""

a.order() # 2

"""
To check condition 2, note that every element of order $39$ in $\text{Th}$ powers to $\text{Th}$-class 3A.
The following element centralises $\langle x_2, x_{3c} \rangle$, has order $39$, and powers to $b$. Therefore, condition 2 holds.
"""

g39 = MM("M<y_0f7h*x_4d8h*d_711h*p_106931325*l_2*p_70118400*l_1*p_190312368*l_1*t_1*l_2*p_80319360*l_1*p_222245808*l_2*t_1*l_1*p_67900800*l_1*p_11552640*l_2*t_1*l_2*p_70118400*l_1*p_179668128>")
g39*x2 == x2*g39 # True
g39*x3c == x3c*g39 # True
g39.order() # 39
g39**13 == b # True

"""
Finally, verify that $g_{3c}/a$ and $h_{3c}/b$ lie in $\langle x_{3c}, x_2 \rangle \cong \sym{3}$:
"""

g3c/a == x3c # True
h3c/b == x2 # True

"""
## $\left( 3^2{:}2 \times \orth+{8}{3} \right) \udot \sym{4}$ <a id="norm3A2"></a>
Generators are given by
"""

g3a2 = MM("M<y_5d6h*x_16d3h*d_0bd2h*p_139920814*l_1*p_2027520*l_1*p_21422781*t_2*l_1*p_960*l_2*p_21797088*t_1*l_2*p_1858560*l_2*p_466896*l_1*p_2841600*t_1*l_2*p_2956800*l_1*p_10858199>")
h3a2 = MM("M<y_3c4h*x_1c28h*d_6fbh*p_207447552*l_2*p_22080*l_1*p_12570864*l_1*t_2*l_2*p_2956800*l_1*p_42714562*l_1*t_2*l_2*p_2956800*l_1*p_21832546>")
L_N = (g3a2, h3a2)

"""
This is the normaliser of a 3A-pure subgroup of the Monster with structure $3^2$.
We claim this particular instance normalises the subgroup generated by
"""

x3 = MM("M<y_3dbh*x_14c9h*d_1c6h*p_238425007*l_2*p_1985280*l_1*p_11174636*l_2>")
y3 = MM("M<y_31eh*x_0fe2h*d_0f91h*p_62189621*l_1*p_2999040*l_1*p_21335268*l_2>")
L_E = (x3, y3)

"""
Note that $x_3$ is as in [Theorem 2.5](#norm3A).  
Firstly, verify that $x_3$ and $y_3 \notin \langle x_3 \rangle$ are
commuting elements of order 3:
"""

# x3 was shown to have order 3 in the proof of Theorem 2.5
y3.order() # 3
x3**y3 == x3 # True
y3 in [x3**i for i in range(1, 3)] # False

"""
It follows that $\langle x_3, y_3 \rangle \cong 3^2$.
As for 3A purity, since 3A is a rational class of $\MM$,
checking that representatives of each cyclic subgroup of
$\langle x_3, y_3 \rangle$ belong to 3A is sufficient.
The proof for the 3A normaliser already established
$x_3 \in \textup{3A}$, while representatives $\left\{ y_3, x_3 y_3, x_3 y_3^2 \right\}$
may be tested using $\chi_\MM$:
"""

reps = [y3, x3*y3, x3*y3**2]
all(x.in_G_x0() for x in reps) # True
[x.chi_G_x0()[0] for x in reps] # [782, 782, 782]

"""
With that settled, show the claimed generators belong to the normaliser of $\langle x_3, y_3 \rangle$.
"""

map_3_2 = map_to_vectors(L_E)
check_normalise(L_E, L_N, group_set=map_3_2) # True

"""
As for showing the entire normaliser of structure $\left( 3^2{:}2 \times \orth+{8}{3} \right) \udot \sym{4}$ is generated,
begin by verifying that the homomorphism induced
by $\langle g_{3a2}, h_{3a2} \rangle$'s action on $\langle x_3, y_3 \rangle$
has an image of size $\left| 2.\sym{4} \right| = 48$:
"""

size_image(L_N, map_3_2, basis=L_E) # 48

"""
It thus suffices to prove that the centraliser $3^2 \times \orth+{8}{3}$ is contained
in $\langle g_{3a2}, h_{3a2} \rangle$. The factor $3^2$ is necessarily
$\langle x_3, y_3 \rangle$, of which both generators appear:
"""

(h3a2*g3a2**3*(h3a2*g3a2)**2)**8 == x3 # True
(h3a2*g3a2*h3a2*g3a2**3*h3a2*g3a2)**8 == y3 # True

"""
We claim that the factor $\orth+{8}{3}$ is generated by the following three elements.
of $C_\MM \left( \langle x_3, y_3 \rangle \right)$.
"""

x13 = (g3a2**2*h3a2)**2*g3a2**4/h3a2**2
x13.order() # 13
x13**x3 == x13**y3 == x13 # True
x2 = ((h3a2*g3a2)**2*h3a2/g3a2)**15
x2.order() # 2
x2**x3 == x2**y3 == x2 # True
g = h3a2**2*(g3a2*h3a2)**2/(h3a2*g3a2)
x14 = (g*x2/g*x2*g)**3
x14.order() # 14
x14**x3 == x14**y3 == x14 # True

"""
Since 13, 2, and 14 are all relatively prime to $3^2$,
these elements certainly lie in the factor $\orth+{8}{3}$
of the centraliser. Moreover, data in the GAP Character Table
Library show that the only maximal subgroup of $\orth+{8}{3}$
with order divisible by both 13 and 14 is $\orth{}{7}{3}$,
in which the centraliser of an element of order 7 has order 14.
The elements $x_{13}$, $x_2$, and $x_{14}$ can therefore be
shown to generate the full group by exhibiting distinct involutions
in $\langle x_{13}, x_2, x_{14} \rangle$ which centralise
the same element of order 7.
"""

# x14**2 and x14**7 are commuting elements of orders 14/2 = 7 and 14/7 = 2
x2**(x14**2) == x2 # True
x2 == x14**7 # False

"""
## $3^{2+5+10}{:}\left( \MT{11} \times 2.\sym{4} \right)$ <a id="norm3B2"></a>
Generators are given by
"""

g3b2 = MM("M<y_1c6h*x_105dh*d_0beh*p_82157098*l_2*p_1943040*l_2*p_1164*t_2*l_2*p_2344320*l_2*p_33456440*l_2*t_1*l_2*p_2956800*l_1*p_32089527*l_2*t_1*l_1*p_2999040*l_1*p_6721*t_2*l_2*p_2956800*l_1*p_43171556*t_1*l_2*p_1394880*l_2*p_1152*l_1*p_1162560*t_2*l_2*p_5760*l_1*t_1*l_1*p_1499520*l_1*p_42733803>")
h3b2 = MM("M<y_2eh*x_1a4ah*d_0c25h*p_13369244*l_2*p_2386560*l_2*p_32572328*l_1*t_2*l_1*p_1457280*l_2*p_21907639*l_2*t_1*l_2*p_1393920*l_1*p_10665792*l_1*p_4734720*t_2*l_2*p_1943040*l_2*p_64126679*t_1*l_1*p_1499520*l_2*p_106702675*t_2*l_2*p_2830080*l_2*p_85336725*t_2*l_1*p_1499520*l_2*p_96464240>")
L_N = (g3b2, h3b2)

"""
This is the normaliser of a certain conjugacy class of 3B-pure $3^2$s in the Monster.
We claim this particular instance normalises the subgroup generated by $x_{3b}$ and $y_{3b}$
from [Theorem 2.6](#norm3B):
"""

x3b = MM("M<y_5d4h*x_17efh*d_0f7eh*p_183231946*l_2*p_2787840*l_2*p_22759172>")
y3b = MM("M<y_4ech*x_0aeeh*d_83bh*p_240916280*l_2*p_2597760*l_1*p_169605*t_2*l_1*p_2027520*l_1*p_22750595*t_2*l_1*p_2640000*l_1*p_178009*t_2*l_1*p_960*l_2*p_53815392*t_2*l_1*p_1415040*l_1*p_2256*l_2*p_76800*t_2*l_2*p_8004480*l_2*p_63909120>")
L_E = (x3b, y3b)

"""
Firstly, recall from the proof of [Theorem 2.6](#norm3B) that $x_{3b}$ belongs
to conjugacy class 3B and $y_{3b} \notin \langle x_{3b} \rangle$ is
an element of order 3 that commutes with $x_{3b}$. The group
$\langle x_{3b}, y_{3b} \rangle$ thus has structure $3^2$; that it is
a suitable $3^2$ for the desired subgroup will be established
in the process of proving that $\langle g_{3b}, h_{3b} \rangle =
    \nma{x_{3b2}, y_{3b2}}$.

Show the claimed generators belong to the normaliser of
$\langle x_{3b}, y_{3b} \rangle$ and $g_{3b2}$ has order 88:
"""

map_3_2 = map_to_vectors(L_E)
check_normalise(L_E, L_N, group_set=map_3_2) # True
g3b2.order() # 88

"""
By Theorem 5.2 of Wilson's odd local subgroups paper,
the normaliser of any group of structure $3^2$ is a subgroup
of a maximal 3-local subgroup of structure $3 \udot \FI$, $3^{1+12} \udot 2 \udot \SZ{:}2$,
$\left( 3^2{:}2 \times \orth+{8}{3} \right) \udot \sym{4}$, $3^{2+5+10}{:}\left( \MT{11} \times 2.\sym{4} \right)$, or $3^8 \udot \orth-{8}{3}.2$. Data in the GAP Character
Table Library show that $\FI$, $\SZ$, $\orth+{8}{3}$, and
$\orth-{8}{3}$ lack elements of orders 44, 22, 11, and 11, respectively,
so that only the fourth 3-local subgroup can contain elements of order 88.
It follows that $N_\MM \left( \langle x_{3b}, y_{3b} \rangle \right)$
is a subgroup of a maximal 3-local subgroup of $\MM$ with structure $3^{2+5+10}{:}\left( \MT{11} \times 2.\sym{4} \right)$.

To show that it is in fact such a group generated by $g_{3b2}, h_{3b2}$,
we first verify that $\langle g_{3b2}, h_{3b2} \rangle$ contains a subgroup of
$\cma{x_{3b}, y_{3b}}$ of order at least $\left| 3^{2+5+10}{:}\MT{11} \right| =
    3^{17} \left| \MT{11} \right|$. Check $a = h_{3b2}^6$ and
$b = \left( g_{3b2}^8 h_{3b2}^3 g_{3b2}^{32} \right)^2$ commute
with $x_{3b}, y_{3b}$ and generate a group of shape $\MT{11}$:
"""

a = MM("M<y_505h*x_15ech*d_0c61h*p_228858934*l_2*p_3256320*l_2*t_2*l_1*p_2027520*l_1*p_11597987*l_1*t_2*l_1*p_2027520*l_1*p_22816917*l_2*t_2*l_1*p_2027520*l_1*p_10593*t_1*l_2*p_6084480*t_1*l_1*p_1499520*l_2*p_42667430*t_1*l_2*p_1457280*l_1*p_50125*t_1*l_2*p_2787840*l_2*p_12485>")
b = MM("M<y_111h*x_0f22h*d_0d97h*p_164778853*l_2*p_1943040*l_2*p_22350273*l_2*t_1*l_2*p_1985280*l_1*p_10665830*l_2*t_2*l_2*p_1394880*l_2*p_22272*l_1*p_1549440*t_2*l_2*p_2344320*l_2*p_2816215*t_1*l_2*p_1943040*l_2*p_127989696*t_1*l_2*p_1985280*l_1*p_64016114*t_2*l_1*p_1499520*l_1*p_43598819>")

a == h3b2**6 # True
b == (g3b2**8*h3b2**3*g3b2**32)**2 # True
x3b**a == x3b**b == x3b # True
y3b**a == y3b**b == y3b # True
test_m11(a, b) # True

"""
As for the factor of $3^{17}$, recall from the proof of
[Theorem 2.6](#norm3B) that $x_{3b}$, $y_{3b}$, and
certain $\ell, \left\{ g_i \right\}_{i=1}^5,
    \left\{ h_i \right\}_{i=1}^5$, $\sigma$ satisfy the conditions
for Lemma 2.2 with $p = 3$ and $k = 5$. It follows that
$x_{3b}$, $y_{3b}$, $\left\{ g_i \right\}$, $\left\{ h_i \right\}$,
and their conjugates by $\sigma$ generate a 3-group
normal in $\cma{x_{3b}, y_{3b}}$ of order at least $3^{2+5+5+5} = 3^{17}$
(noting the conjugates $g_i^{\sigma}$ cannot be counted in the exponent).
Expressing each of these elements as a word in $g_{3b2}, h_{3b2}$ therefore
yields the desired factor.
"""

# The given elements
gs = (
    MM("M<y_58eh*x_8fh*d_2c9h*p_76285619*l_2*p_1457280*l_1*p_32103884*t_2*l_1*p_960*l_2*p_10665888*l_2*p_3763200*t_1*l_1*p_2027520*l_1*p_13020096*l_2*t_1*l_2*p_2956800*l_1*p_53349541*t_2*l_2*p_1415040*l_1*p_466800*l_2*p_3465600*t_1*l_2*p_2386560*l_2*p_42717489*t_2*l_2*p_2956800*l_1*p_85370418>"),
    MM("M<y_662h*x_17f8h*d_0ff0h*p_233651083*l_1*p_543360*t_1*l_1*p_2027520*l_1*p_47239*t_2*l_2*p_1457280*l_1*p_578263*t_1*l_1*p_15100800*t_2*l_2*p_2597760*l_1*p_21426569*t_1*l_2*p_2597760*l_1*p_64078688*t_1*l_1*p_1499520*l_1*p_85328065>"),
    MM("M<y_778h*x_0a7dh*d_0b20h*p_61290019*l_2*p_234220800*t_2*l_2*p_1943040*l_2*p_2352323*l_1*t_2*l_1*p_1858560*l_2*p_23280*l_1*p_2411520*t_2*l_1*p_3823680*t_1*l_1*p_68787840*l_1*p_108704736*t_1*l_2*p_2956800*l_1*p_53814185*t_1*l_2*p_59917440*l_1*p_127776096>"),
    MM("M<y_91h*x_550h*d_8f8h*p_131387342*l_2*p_1900800*l_2*p_21865336*l_2*t_1*l_1*p_1415040*l_1*p_23328*l_2*p_1520640*t_2*l_2*p_1943040*l_2*p_2414887*l_1*t_2*l_1*p_1099200*t_2*l_2*p_2830080*l_2*p_42796362*t_2*l_2*p_1943040*l_2*p_85816867*t_2*l_2*p_2956800*l_1*p_53381152>"),
    MM("M<y_36dh*x_0f60h*d_312h*p_128810854*l_1*p_2640000*l_1*p_21865335*t_1*l_2*p_2830080*l_2*p_21370*l_2*t_2*l_2*p_1985280*l_1*p_32504018*l_2*t_2*l_2*p_1943040*l_2*p_12176258*l_2*t_1*l_2*p_1900800*l_2*p_5763*t_2*l_2*p_2830080*l_2*p_42671248>")
)
hs = (
    MM("M<y_0abh*x_13d0h*d_0f66h*p_197048161*l_1*p_1858560*l_1*p_465936*l_2*p_510720*t_1*l_2*p_24000*l_2*p_488160*t_1*l_2*p_2386560*l_2*p_64036498*t_2*l_2*p_2787840*l_2*p_2800905*l_2*t_2*l_2*p_2787840*l_2*p_11554*t_2*l_1*p_2640000*l_1*p_13458>"),
    MM("M<y_119h*x_75bh*d_8bbh*p_203279177*l_2*p_2830080*l_2*p_10671544*t_1*l_1*p_2027520*l_1*p_22307968*l_1*t_1*l_2*p_2956800*l_1*p_21888592*l_2*t_1*l_1*p_1499520*l_2*p_42677961*t_2*l_2*p_2830080*l_2*p_21336113*t_1*l_1*p_1457280*l_2*p_12994999*l_1*t_1*l_2*p_2830080*l_2*p_21345778>"),
    MM("M<y_1a3h*x_0b74h*d_0a38h*p_201631922*l_2*p_2344320*l_2*p_33013873*l_2*t_1*l_1*p_1499520*l_2*p_467786*l_1*t_2*l_2*p_1393920*l_2*p_3120*l_1*p_1206720*t_1*l_2*p_1900800*l_2*p_3104*t_2*l_2*p_1858560*l_1*p_10665888*l_1*p_699840*t_2*l_2*p_5641920*l_1*t_1*l_2*p_1900800*l_2*p_137698>"),
    MM("M<y_0f2h*x_1c21h*d_0e0fh*p_228919392*l_1*p_80319360*l_2*p_231116160*t_1*l_2*p_1900800*l_2*p_22774569*l_2*t_1*l_2*p_2787840*l_2*p_33013910*l_1*t_1*l_2*p_1943040*l_2*p_33460438*l_1*t_2*l_1*p_2027520*l_1*p_5761*t_2*l_2*p_2830080*l_2*p_42798259>"),
    MM("M<y_4b1h*x_1162h*d_3b3h*p_195698166*l_2*p_2956800*l_1*p_32978354*l_2*t_1*l_1*p_2640000*l_1*p_2859335*l_2*t_1*l_2*p_1900800*l_2*p_2388161*l_1*t_2*l_1*p_467520*l_1*p_85056*t_2*l_1*p_1499520*l_1*p_85820694*t_2*l_2*p_1943040*l_2*p_85367645*t_2*l_2*p_1943040*l_2*p_42729963>")
)
σ = MM("M<y_46ch*x_19b9h*d_9f4h*p_43971768*l_1*p_2640000*l_1*p_11712608*l_2*t_1*l_2*p_2597760*l_1*p_11222741*t_1*l_2*p_1943040*l_2*p_11225569*t_2*l_2*p_2386560*l_2*p_10741665*t_1*l_2*p_1985280*l_1*p_86283414*l_1*p_10688640*t_2*l_2*p_1858560*l_1*p_3168*l_2*p_10436160>")

σ == (g3b2*h3b2)**9 # True

c = a**σ/a
cnj = [h3b2*g3b2, g3b2**3, h3b2*g3b2*h3b2, g3b2**3*h3b2, g3b2*h3b2**2*g3b2, h3b2*g3b2*h3b2**2, h3b2**2*g3b2**2, g3b2**3*h3b2**2, g3b2*h3b2*g3b2**3, h3b2*g3b2**2*h3b2*g3b2, h3b2*g3b2*h3b2**3]
cnj = [c**x for x in cnj]
x3b == comm(cnj[3], cnj[1]) # True
y3b == cnj[2]**2*cnj[3]*cnj[4]**2*cnj[6]*cnj[10]**2 # True

mat = [[1, 2, 0, 1, 0, 2, 0, 2, 0, 0, 0],
       [2, 0, 1, 2, 2, 2, 0, 2, 2, 0, 0],
       [2, 2, 2, 2, 1, 2, 2, 2, 0, 0, 2],
       [0, 1, 2, 2, 1, 0, 2, 2, 0, 0, 0],
       [2, 2, 2, 1, 2, 1, 1, 0, 0, 1, 2],
       [0, 1, 1, 2, 1, 1, 2, 0, 0, 0, 2],
       [0, 1, 2, 1, 1, 1, 1, 1, 0, 2, 0],
       [1, 2, 0, 1, 2, 2, 2, 0, 1, 2, 0],
       [2, 1, 0, 0, 0, 1, 0, 2, 2, 2, 1],
       [1, 1, 2, 0, 2, 1, 0, 2, 1, 0, 2]]

x3b_numbers = [0, 1, 1, 2, 0, 2, 1, 0, 0, 2]
ghs_values = []
for seq, x3b_num in zip(mat, x3b_numbers):
    x = x3b**x3b_num
    for cnj_el, power in zip(cnj, seq):
        x *= cnj_el**power
    
    ghs_values.append(x)

all(x == y for x, y in zip(gs + hs, ghs_values)) # True

"""
Normality guarantees $\MT{11}$, which is a simple group, either lies
in this 3-group or intersects it in the trivial group. The former possibility
is excluded by the fact that $\MT{11}$ cannot lie inside a 3-group, so that
the two subgroups of the centraliser found thus far together generate
a subgroup of order at least $3^{17} \left| \MT{11} \right| =
    \left| 3^{2+5+10}.\MT{11} \right|$.

To expand this by a factor of $\left| 2.\sym{4} \right| = 48$, it suffices
to consider the homomorphism induced by $\langle g_{3b2}, h_{3b2} \rangle$'s
conjugation action on $\langle x_{3b}, y_{3b} \rangle$. Enumerating its image
reveals
"""

size_image(L_N, map_3_2, basis=L_E) # 48

"""
It follows that $\langle g_{3b2}, h_{3b2} \rangle \le \nma{x_{3b}, y_{3b}}$
has order at least $3^{17} \left| \MT{11} \right| \cdot 48 = \left| 3^{2+5+10}{:}\left( \MT{11} \times 2.\sym{4} \right) \right|$.
But the normaliser of $\langle x_{3b}, y_{3b} \rangle$ lies inside a maximal subgroup of $\MM$
with this structure; it therefore *is* such a maximal subgroup, generated by $g_{3b2}$
and $h_{3b2}$.
"""

"""
## $3^{3+2+6+6}{:}\left( \psl{3}{3} \times \sdih{16} \right)$ <a id="norm3B3"></a>
Generators are given by
"""

g3b3 = MM("M<y_0a1h*x_1f62h*d_0a51h*p_222859169*l_1*p_2640000*l_1*p_33414121*l_1*t_2*l_1*p_2640000*l_1*p_12151253*l_2*t_2*l_2*p_1920*l_1*p_464880*l_1*p_530880*t_2*l_1*p_1499520*l_2*p_42755929*t_2*l_2*p_1900800*l_2*p_6723*t_2*l_1*p_2640000*l_1*p_69282*t_1*l_2*p_2830080*l_2*p_86257539>")
h3b3 = MM("M<y_455h*x_0feh*d_0c1ch*p_101629354*l_2*p_89189760*t_2*l_2*p_70561920*l_2*p_212488368*l_1*t_2*l_2*p_80762880*l_1*p_209827200*l_2*t_1*l_2*p_2597760*l_1*p_85328064*t_1*l_1*p_1907520*t_2*l_2*p_1393920*l_1*p_53793024*t_2*l_2*p_2386560*l_2*p_11218865*t_1*l_2*p_57699840*l_2*p_86972352>")
L_N = (g3b3, h3b3)

"""
This is the normaliser of a certain conjugacy class of 3B-pure $3^3$s in the Monster.
We claim this particular instance normalises the subgroup generated by
"""

x3b = MM("M<y_5d4h*x_17efh*d_0f7eh*p_183231946*l_2*p_2787840*l_2*p_22759172>")
y3b = MM("M<y_4ech*x_0aeeh*d_83bh*p_240916280*l_2*p_2597760*l_1*p_169605*t_2*l_1*p_2027520*l_1*p_22750595*t_2*l_1*p_2640000*l_1*p_178009*t_2*l_1*p_960*l_2*p_53815392*t_2*l_1*p_1415040*l_1*p_2256*l_2*p_76800*t_2*l_2*p_8004480*l_2*p_63909120>")
z3b = MM("M<y_89h*x_0b83h*d_47fh*p_183258749*l_2*p_1985280*l_1*p_43685419*t_1*l_2*p_2830080*l_2*p_21336201*t_1*l_1*p_1499520*l_2*p_43150478*t_2*l_2*p_1985280*l_1*p_64007382*t_1*l_2*p_1920*l_2*p_2160*l_2*p_2557440*t_1*l_2*p_2956800*l_1*p_96019794>")
L_E = (x3b, y3b, z3b)

"""
Note that $x_{3b}$ and $y_{3b}$ are as in [Theorem 2.6](#norm3B) and
[Theorem 2.9](#norm3B2). It was shown in the proof of the former that
$\langle x_{3b}, y_{3b} \rangle$ is an elementary abelian group
embedded in the normal subgroup $3^{1+12}$ of $\nma{x_{3b}}$. Hence,
if $z_{3b} \in \cma{x_{3b}, y_{3b}}$ is conjugate to $y_{3b}$
in that normaliser, $\langle x_{3b}, y_{3b}, z_{3b} \rangle$ is
an elementary abelian subgroup of $3^{1+12}$ containing the centre.
"""

x3b*z3b == z3b*x3b # True
y3b*z3b == z3b*y3b # True

c = g3b3*h3b3**3*g3b3*h3b3*g3b3
x3b*c == c*x3b # True
y3b**c == z3b # True

"""
Theorem 6.5 of Wilson's odd local subgroups paper thus guarantees
$\nma{x_{3b}, y_{3b}, z_{3b}}$ lies in a maximal subgroup of structure
$3^{1+12} \udot 2 \udot \SZ{:}2$, $3^{2+5+10}{:}\left( \MT{11} \times 2.\sym{4} \right)$, or $3^{3+2+6+6}{:}\left( \psl{3}{3} \times \sdih{16} \right)$. Only the third of these
can contain elements of order 104 --- $\SZ.2$ and $\MT{11}$ do not
contain elements of order 104 or 13, respectively --- so exhibiting
an element of this order eliminates the first two possibilities.
"""

map_3_3 = map_to_vectors(L_E)
check_normalise(L_E, L_N, group_set=map_3_3) # True
h3b3.order() # 104

"""
To show that $g_{3b3}, h_{3b3}$ in fact generate the full $3^{3+2+6+6}{:}\left( \psl{3}{3} \times \sdih{16} \right)$,
we first verify that $\langle g_{3b3}, h_{3b3} \rangle$ contains a subgroup of
$\cma{x_{3b}, y_{3b}, z_{3b}}$ of order at least
$\left| 3^{3+2+6+6}{:}\dih{8} \right| = 3^{17} \cdot 8$. Express all
except $h_2$ and $h_2^{\sigma}$ of
$x_{3b}$, $y_{3b}$, $\left\{ g_i \right\}_{i = 1}^5$,
$\left\{ h_i \right\}_{i = 1}^5$, and
$\left\{ h_i^{\sigma} \right\}_{i = 1}^5$ defined in the proof
of [Theorem 2.6](#norm3B) as words in $g_{3b3}, h_{3b3}$ for a 3-group
of order at least $3^{2+5+4+4} = 3^{15}$ (using Lemma 2.2):
"""

# The given elements
gs = (
    MM("M<y_58eh*x_8fh*d_2c9h*p_76285619*l_2*p_1457280*l_1*p_32103884*t_2*l_1*p_960*l_2*p_10665888*l_2*p_3763200*t_1*l_1*p_2027520*l_1*p_13020096*l_2*t_1*l_2*p_2956800*l_1*p_53349541*t_2*l_2*p_1415040*l_1*p_466800*l_2*p_3465600*t_1*l_2*p_2386560*l_2*p_42717489*t_2*l_2*p_2956800*l_1*p_85370418>"),
    MM("M<y_662h*x_17f8h*d_0ff0h*p_233651083*l_1*p_543360*t_1*l_1*p_2027520*l_1*p_47239*t_2*l_2*p_1457280*l_1*p_578263*t_1*l_1*p_15100800*t_2*l_2*p_2597760*l_1*p_21426569*t_1*l_2*p_2597760*l_1*p_64078688*t_1*l_1*p_1499520*l_1*p_85328065>"),
    MM("M<y_778h*x_0a7dh*d_0b20h*p_61290019*l_2*p_234220800*t_2*l_2*p_1943040*l_2*p_2352323*l_1*t_2*l_1*p_1858560*l_2*p_23280*l_1*p_2411520*t_2*l_1*p_3823680*t_1*l_1*p_68787840*l_1*p_108704736*t_1*l_2*p_2956800*l_1*p_53814185*t_1*l_2*p_59917440*l_1*p_127776096>"),
    MM("M<y_91h*x_550h*d_8f8h*p_131387342*l_2*p_1900800*l_2*p_21865336*l_2*t_1*l_1*p_1415040*l_1*p_23328*l_2*p_1520640*t_2*l_2*p_1943040*l_2*p_2414887*l_1*t_2*l_1*p_1099200*t_2*l_2*p_2830080*l_2*p_42796362*t_2*l_2*p_1943040*l_2*p_85816867*t_2*l_2*p_2956800*l_1*p_53381152>"),
    MM("M<y_36dh*x_0f60h*d_312h*p_128810854*l_1*p_2640000*l_1*p_21865335*t_1*l_2*p_2830080*l_2*p_21370*l_2*t_2*l_2*p_1985280*l_1*p_32504018*l_2*t_2*l_2*p_1943040*l_2*p_12176258*l_2*t_1*l_2*p_1900800*l_2*p_5763*t_2*l_2*p_2830080*l_2*p_42671248>")
)
hs = (
    MM("M<y_0abh*x_13d0h*d_0f66h*p_197048161*l_1*p_1858560*l_1*p_465936*l_2*p_510720*t_1*l_2*p_24000*l_2*p_488160*t_1*l_2*p_2386560*l_2*p_64036498*t_2*l_2*p_2787840*l_2*p_2800905*l_2*t_2*l_2*p_2787840*l_2*p_11554*t_2*l_1*p_2640000*l_1*p_13458>"),
    MM("M<y_119h*x_75bh*d_8bbh*p_203279177*l_2*p_2830080*l_2*p_10671544*t_1*l_1*p_2027520*l_1*p_22307968*l_1*t_1*l_2*p_2956800*l_1*p_21888592*l_2*t_1*l_1*p_1499520*l_2*p_42677961*t_2*l_2*p_2830080*l_2*p_21336113*t_1*l_1*p_1457280*l_2*p_12994999*l_1*t_1*l_2*p_2830080*l_2*p_21345778>"),
    MM("M<y_1a3h*x_0b74h*d_0a38h*p_201631922*l_2*p_2344320*l_2*p_33013873*l_2*t_1*l_1*p_1499520*l_2*p_467786*l_1*t_2*l_2*p_1393920*l_2*p_3120*l_1*p_1206720*t_1*l_2*p_1900800*l_2*p_3104*t_2*l_2*p_1858560*l_1*p_10665888*l_1*p_699840*t_2*l_2*p_5641920*l_1*t_1*l_2*p_1900800*l_2*p_137698>"),
    MM("M<y_0f2h*x_1c21h*d_0e0fh*p_228919392*l_1*p_80319360*l_2*p_231116160*t_1*l_2*p_1900800*l_2*p_22774569*l_2*t_1*l_2*p_2787840*l_2*p_33013910*l_1*t_1*l_2*p_1943040*l_2*p_33460438*l_1*t_2*l_1*p_2027520*l_1*p_5761*t_2*l_2*p_2830080*l_2*p_42798259>"),
    MM("M<y_4b1h*x_1162h*d_3b3h*p_195698166*l_2*p_2956800*l_1*p_32978354*l_2*t_1*l_1*p_2640000*l_1*p_2859335*l_2*t_1*l_2*p_1900800*l_2*p_2388161*l_1*t_2*l_1*p_467520*l_1*p_85056*t_2*l_1*p_1499520*l_1*p_85820694*t_2*l_2*p_1943040*l_2*p_85367645*t_2*l_2*p_1943040*l_2*p_42729963>")
)
σ = MM("M<y_46ch*x_19b9h*d_9f4h*p_43971768*l_1*p_2640000*l_1*p_11712608*l_2*t_1*l_2*p_2597760*l_1*p_11222741*t_1*l_2*p_1943040*l_2*p_11225569*t_2*l_2*p_2386560*l_2*p_10741665*t_1*l_2*p_1985280*l_1*p_86283414*l_1*p_10688640*t_2*l_2*p_1858560*l_1*p_3168*l_2*p_10436160>")

c = (g3b3*h3b3)**4

# The elements to be exhibited were shown to commute with x3b, y3b above
# It only remains to handle z3b; since centralisers are normal subgroups of
# normalisers, we check z3b*c = c*z3b and express the remaining elements
# as words in conjugates of c.
c*z3b == z3b*c # True

cnj = [c**g3b3*c, c**(g3b3**2)/c**h3b3, c**(h3b3*g3b3)*c**h3b3/c, c**(h3b3**2)*c**h3b3*c]
cnj += [c**(g3b3**3)/c**h3b3/c, c**(g3b3**2*h3b3)*c**h3b3/c, c**(h3b3*g3b3**2)*c/c**h3b3, c**(h3b3*g3b3*h3b3)/c**h3b3/c]

# Speed-up
for x in cnj:
    x.reduce()

cnj = [comm(x, y).reduce() for i, x in enumerate(cnj[:5]) for y in cnj[:i]][:7] + cnj + [c, c**(h3b3**2)]

mat = [[2, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
       [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
       [1, 2, 2, 2, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
       [1, 2, 0, 2, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
       [0, 1, 1, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
       [0, 2, 1, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
       [0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
       [0, 2, 0, 0, 1, 0, 2, 1, 0, 0, 2, 1, 1, 1, 1, 0, 0],
       [2, 0, 2, 0, 2, 1, 0, 0, 2, 0, 1, 2, 1, 1, 0, 0, 0],
       [1, 0, 1, 2, 0, 0, 0, 0, 2, 2, 2, 1, 2, 1, 1, 0, 0],
       [2, 1, 0, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 2, 2, 0, 0],
       [1, 1, 2, 0, 1, 2, 0, 0, 0, 1, 1, 1, 0, 1, 2, 0, 0],
       [1, 1, 1, 2, 2, 1, 1, 0, 1, 2, 1, 1, 0, 1, 1, 0, 0],
       [1, 2, 0, 1, 0, 1, 2, 1, 1, 2, 0, 1, 2, 2, 0, 0, 0],
       [1, 2, 0, 2, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0],
       [2, 2, 2, 2, 2, 0, 0, 2, 1, 1, 0, 2, 0, 2, 0, 1, 0],
       [0, 0, 2, 0, 1, 2, 0, 1, 0, 2, 1, 2, 2, 1, 0, 0, 1]]

ghs_values = []
for seq in mat:
    x = e
    for cnj_el, power in zip(cnj, seq):
        x *= cnj_el**power
    
    ghs_values.append(x)

all(x == y for x, y in zip((x3b, y3b, *gs, *hs[:1], *hs[2:], *(x**σ for x in hs[:1] + hs[2:])), ghs_values)) # True

"""
The above loop generated two elements of $\cma{x_{3b}, y_{3b}, z_{3b}}$ in surplus
to the 15 analysed. Show that these generate a subgroup of $9 = 3^2$ elements
of the group $\langle a, b \rangle \cong \MT{11}$ constructed as part of the proof of
[Theorem 2.9](#norm3B2).
"""

len(ghs_values) # 17

# The elements referenced
a = MM("M<y_505h*x_15ech*d_0c61h*p_228858934*l_2*p_3256320*l_2*t_2*l_1*p_2027520*l_1*p_11597987*l_1*t_2*l_1*p_2027520*l_1*p_22816917*l_2*t_2*l_1*p_2027520*l_1*p_10593*t_1*l_2*p_6084480*t_1*l_1*p_1499520*l_2*p_42667430*t_1*l_2*p_1457280*l_1*p_50125*t_1*l_2*p_2787840*l_2*p_12485>")
b = MM("M<y_111h*x_0f22h*d_0d97h*p_164778853*l_2*p_1943040*l_2*p_22350273*l_2*t_1*l_2*p_1985280*l_1*p_10665830*l_2*t_2*l_2*p_1394880*l_2*p_22272*l_1*p_1549440*t_2*l_2*p_2344320*l_2*p_2816215*t_1*l_2*p_1943040*l_2*p_127989696*t_1*l_2*p_1985280*l_1*p_64016114*t_2*l_1*p_1499520*l_1*p_43598819>")

size_image(ghs_values[-2:]) # 9
ghs_values[-1] == (a*b*a*(b**2*a)**2)**2 # True
ghs_values[-2] == ((b*a)**3*(b**2*a)**2*b*a)**2 # True

"""
Noting that $\MT{11}$ was proven not to intersect the normal subgroup
$3^{2+5+10}$ of $\cma{x_{3b}, y_{3b}}$ to which the other 15 elements
of `ghs_values` belong, the 17 elements together generate a 3-group
of order at least $3^{17}$.

The remaining factor of 8 in $3^{17} \cdot 8$ may then be obtained
by demonstrating $\cma{x_{3b}, y_{3b}, z_{3b}}$ must have an order
divisible by 8. This follows from the Orbit-Stabiliser Theorem
upon enumerating $h_1^{\langle g_{3b3}^{39}, h_{3b3}^{26} \rangle}$:
"""

# Make sure g3b3^39 and h3b3^26 are actually in the centraliser
all(x*y == y*x for x in (g3b3**39, h3b3**26) for y in (x3b, y3b, z3b)) # True

size_image((g3b3**39, h3b3**26), (lambda x: as_int(hs[0]**x))) # 72

"""
Finally, the remaining factor of $2 \left| \psl{3}{3} \right| = 11232$
in the group order emerges from the homomorphism induced
by $\langle g_{3b3}, h_{3b3} \rangle$'s conjugation action
on $\langle x_{3b}, y_{3b} \rangle$.
"""

size_image(L_N, map_3_3, basis=L_E) # 11232

"""
It follows that $\langle g_{3b2}, h_{3b2} \rangle \le \nma{x_{3b}, y_{3b}, z_{3b}}$
has order at least $3^{17} \cdot 8 \cdot 2 \left| \psl{3}{3} \right| =
    \left| 3^{3+2+6+6}{:}\left( \psl{3}{3} \times \sdih{16} \right) \right|$. But the normaliser of
$\langle x_{3b}, y_{3b}, z_{3b3} \rangle$ lies inside a maximal subgroup of $\MM$
with this structure; it therefore *is* such a maximal subgroup, generated by $g_{3b3}$
and $h_{3b3}$.
"""

"""
## $3^8 \udot \orth-{8}{3}.2$ <a id="norm3Ark"></a>

Generators for this maximal subgroup are given by
"""

g38 = MM("M<y_5b9h*x_0a76h*d_0e32h*p_177893787*l_1*p_1499520*l_2*p_21796210*t_1*l_1*p_1499520*l_2*p_13056500*l_1*t_1*l_1*p_1858560*l_1*p_465840*l_2*p_679680*t_1*l_2*p_1457280*l_1*p_1123761*t_2*l_1*p_2027520*l_1*p_96038951*l_1*p_44160*t_1*l_1*p_1499520*l_2*p_64007328*l_2*p_11658240>")
h38 = MM("M<y_18h*x_187h*d_0cb6h*p_220049255*l_2*p_2386560*l_2*p_42858*t_1*l_2*p_2597760*l_1*p_32509911*t_2*l_2*p_2787840*l_2*p_133802*t_1*l_2*p_1943040*l_2*p_21546839*t_2*l_2*p_1394880*l_1*p_10665792*l_1*p_2093760*t_2*l_2*p_1943040*l_2*p_106662273*t_1*l_1*p_1499520*l_1*p_42832004>")
L_N = (g38, h38)

"""
The maximal subgroups of $\MM$ with this structure are the normalisers of
certain elementary abelian subgroups of order $3^8$. We claim this particular instance
normalises $\langle x_{3b}, y_{3b}, g_1, g_2, g_3, g_4, h_5, h_5^{\sigma} \rangle$,
where $x_{3b}$, $y_{3b}$, $\left\{ g_i \right\}_{i=1}^5$,
$\left\{ h_i \right\}_{i=1}^5$, and $\sigma$ are as in the proof
of [Theorem 2.6](#norm3B):
"""

x3b = MM("M<y_5d4h*x_17efh*d_0f7eh*p_183231946*l_2*p_2787840*l_2*p_22759172>")
y3b = MM("M<y_4ech*x_0aeeh*d_83bh*p_240916280*l_2*p_2597760*l_1*p_169605*t_2*l_1*p_2027520*l_1*p_22750595*t_2*l_1*p_2640000*l_1*p_178009*t_2*l_1*p_960*l_2*p_53815392*t_2*l_1*p_1415040*l_1*p_2256*l_2*p_76800*t_2*l_2*p_8004480*l_2*p_63909120>")
gs = (
    MM("M<y_58eh*x_8fh*d_2c9h*p_76285619*l_2*p_1457280*l_1*p_32103884*t_2*l_1*p_960*l_2*p_10665888*l_2*p_3763200*t_1*l_1*p_2027520*l_1*p_13020096*l_2*t_1*l_2*p_2956800*l_1*p_53349541*t_2*l_2*p_1415040*l_1*p_466800*l_2*p_3465600*t_1*l_2*p_2386560*l_2*p_42717489*t_2*l_2*p_2956800*l_1*p_85370418>"),
    MM("M<y_662h*x_17f8h*d_0ff0h*p_233651083*l_1*p_543360*t_1*l_1*p_2027520*l_1*p_47239*t_2*l_2*p_1457280*l_1*p_578263*t_1*l_1*p_15100800*t_2*l_2*p_2597760*l_1*p_21426569*t_1*l_2*p_2597760*l_1*p_64078688*t_1*l_1*p_1499520*l_1*p_85328065>"),
    MM("M<y_778h*x_0a7dh*d_0b20h*p_61290019*l_2*p_234220800*t_2*l_2*p_1943040*l_2*p_2352323*l_1*t_2*l_1*p_1858560*l_2*p_23280*l_1*p_2411520*t_2*l_1*p_3823680*t_1*l_1*p_68787840*l_1*p_108704736*t_1*l_2*p_2956800*l_1*p_53814185*t_1*l_2*p_59917440*l_1*p_127776096>"),
    MM("M<y_91h*x_550h*d_8f8h*p_131387342*l_2*p_1900800*l_2*p_21865336*l_2*t_1*l_1*p_1415040*l_1*p_23328*l_2*p_1520640*t_2*l_2*p_1943040*l_2*p_2414887*l_1*t_2*l_1*p_1099200*t_2*l_2*p_2830080*l_2*p_42796362*t_2*l_2*p_1943040*l_2*p_85816867*t_2*l_2*p_2956800*l_1*p_53381152>"),
    MM("M<y_36dh*x_0f60h*d_312h*p_128810854*l_1*p_2640000*l_1*p_21865335*t_1*l_2*p_2830080*l_2*p_21370*l_2*t_2*l_2*p_1985280*l_1*p_32504018*l_2*t_2*l_2*p_1943040*l_2*p_12176258*l_2*t_1*l_2*p_1900800*l_2*p_5763*t_2*l_2*p_2830080*l_2*p_42671248>")
)
hs = (
    MM("M<y_0abh*x_13d0h*d_0f66h*p_197048161*l_1*p_1858560*l_1*p_465936*l_2*p_510720*t_1*l_2*p_24000*l_2*p_488160*t_1*l_2*p_2386560*l_2*p_64036498*t_2*l_2*p_2787840*l_2*p_2800905*l_2*t_2*l_2*p_2787840*l_2*p_11554*t_2*l_1*p_2640000*l_1*p_13458>"),
    MM("M<y_119h*x_75bh*d_8bbh*p_203279177*l_2*p_2830080*l_2*p_10671544*t_1*l_1*p_2027520*l_1*p_22307968*l_1*t_1*l_2*p_2956800*l_1*p_21888592*l_2*t_1*l_1*p_1499520*l_2*p_42677961*t_2*l_2*p_2830080*l_2*p_21336113*t_1*l_1*p_1457280*l_2*p_12994999*l_1*t_1*l_2*p_2830080*l_2*p_21345778>"),
    MM("M<y_1a3h*x_0b74h*d_0a38h*p_201631922*l_2*p_2344320*l_2*p_33013873*l_2*t_1*l_1*p_1499520*l_2*p_467786*l_1*t_2*l_2*p_1393920*l_2*p_3120*l_1*p_1206720*t_1*l_2*p_1900800*l_2*p_3104*t_2*l_2*p_1858560*l_1*p_10665888*l_1*p_699840*t_2*l_2*p_5641920*l_1*t_1*l_2*p_1900800*l_2*p_137698>"),
    MM("M<y_0f2h*x_1c21h*d_0e0fh*p_228919392*l_1*p_80319360*l_2*p_231116160*t_1*l_2*p_1900800*l_2*p_22774569*l_2*t_1*l_2*p_2787840*l_2*p_33013910*l_1*t_1*l_2*p_1943040*l_2*p_33460438*l_1*t_2*l_1*p_2027520*l_1*p_5761*t_2*l_2*p_2830080*l_2*p_42798259>"),
    MM("M<y_4b1h*x_1162h*d_3b3h*p_195698166*l_2*p_2956800*l_1*p_32978354*l_2*t_1*l_1*p_2640000*l_1*p_2859335*l_2*t_1*l_2*p_1900800*l_2*p_2388161*l_1*t_2*l_1*p_467520*l_1*p_85056*t_2*l_1*p_1499520*l_1*p_85820694*t_2*l_2*p_1943040*l_2*p_85367645*t_2*l_2*p_1943040*l_2*p_42729963>")
)
σ = MM("M<y_46ch*x_19b9h*d_9f4h*p_43971768*l_1*p_2640000*l_1*p_11712608*l_2*t_1*l_2*p_2597760*l_1*p_11222741*t_1*l_2*p_1943040*l_2*p_11225569*t_2*l_2*p_2386560*l_2*p_10741665*t_1*l_2*p_1985280*l_1*p_86283414*l_1*p_10688640*t_2*l_2*p_1858560*l_1*p_3168*l_2*p_10436160>")
L_E = (x3b, y3b, *gs[:4], hs[4], hs[4]**σ)

"""
These were shown above to have order 3, and applying
our $p$-group lemma establishes they generate a 3-group of order at least $3^8$;
check they commute.
"""

# It has already been verified x3b and y3b commute with all the given elements
all(x*y == y*x for i, x in enumerate(L_E[2:]) for y in L_E[2:2+i]) # True

"""
The group therefore has a 3-local subgroup of $\MM$ for a normaliser, which
by Theorem 5.2 of Wilson's odd-local subgroups paper must lie
in a maximal subgroup of $\MM$ with structure $3 \udot \FI$, $3^{1+12} \udot 2 \udot \SZ{:}2$, $\left( 3^2{:}2 \times \orth+{8}{3} \right) \udot \sym{4}$,
$3^{2+5+10}{:}\left( \MT{11} \times 2.\sym{4} \right)$, or $3^8 \udot \orth-{8}{3}.2$. Since only the last of these has an order
divisible by 41, it suffices to show that the normaliser of the given 3-group
contains such an element.
"""

# Take a manual approach to avoid enumerating the entire 3^8
gmat = [[0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 2, 2, 2, 0, 0],
        [0, 2, 1, 0, 0, 0, 0, 1],
        [0, 2, 1, 1, 1, 0, 0, 0],
        [0, 2, 2, 1, 2, 2, 0, 0],
        [1, 0, 1, 2, 0, 0, 0, 2],
        [0, 1, 0, 0, 0, 1, 0, 0],
        [0, 2, 0, 2, 2, 2, 2, 1]]

hmat = [[1, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        [1, 1, 2, 1, 0, 0, 0, 0],
        [1, 1, 2, 0, 0, 2, 0, 0],
        [1, 0, 2, 1, 2, 1, 0, 0],
        [0, 0, 2, 2, 0, 2, 0, 0],
        [2, 1, 1, 1, 0, 0, 2, 0],
        [1, 0, 2, 0, 0, 2, 0, 2]]

g_tests = []
for seq in gmat:
    x = e
    for cnj_el, power in zip(L_E, seq):
        x *= cnj_el**power
    
    g_tests.append(x)

h_tests = []
for seq in hmat:
    x = e
    for cnj_el, power in zip(L_E, seq):
        x *= cnj_el**power
    
    h_tests.append(x)

all(x == u**g38 for x, u in zip(g_tests, L_E)) # True
all(x == u**h38 for x, u in zip(h_tests, L_E)) # True
g38.order() # 41

"""
This incidentally establishes that the claimed generators belong
to the given subgroup's normaliser.

It will follow that $g_{3^8}, h_{3^8}$ generate the entire subgroup of
structure $3^8 \udot \orth-{8}{3}.2$ upon showing that the former group has order
$\left| 3^8 \udot \orth-{8}{3}.2 \right| = 3^8 \left| \orth-{8}{3} \right| \cdot 2$.
The code in `helpers.gap` shows that the homomorphism induced
by $\langle g_{3^8}, h_{3^8} \rangle$'s action on the $3^8$ ---
embedded in $\ling{8}{3}$ using the matrices `gmat` and `hmat` above ---
has an image of structure $orth-{8}{3}.2$. It only remains to account
for the $3^8$ itself, which we do by expressing the generators thereof
in terms of $g_{3^8}, h_{3^8}$.
"""

gh_basis = [((h38**4)**(g38**i)).reduce() for i in range(8)]
mat = [[1, 0, 0, 0, 0, 0, 0, 0],
       [0, 1, 0, 0, 0, 0, 0, 0],
       [1, 2, 2, 1, 1, 0, 0, 2],
       [2, 0, 1, 2, 1, 0, 2, 0],
       [0, 1, 0, 1, 0, 1, 1, 0],
       [1, 2, 1, 0, 2, 2, 0, 0],
       [2, 2, 0, 2, 2, 1, 2, 2],
       [0, 1, 2, 1, 0, 1, 2, 2]]

g_tests = []
for seq in mat:
    x = e
    for i, u in zip(seq, gh_basis):
        x *= u**i
    
    g_tests.append(x)

all(x == u for x, u in zip(L_E, g_tests)) # True

"""
## $\left( \dih{10} \times \HN \right) \udot 2$ <a id="norm5A"></a>
Generators are
"""

g5 = MM("M<y_616h*x_4ceh*d_0ae6h*p_77235292*l_2*p_960*l_2*p_10667856*l_1*p_119040*t_1*l_1*p_360000*t_1*l_1*p_1499520*l_2*p_42713601*t_1*l_1*p_1499520*l_2*p_43257217>")
h5 = MM("M<y_42h*x_197dh*d_91dh*p_149043227*l_2*p_2386560*l_2*p_32567540*l_2*t_2*l_1*p_1499520*l_1*p_583094*t_2*l_2*p_1943040*l_2*p_42709851*t_1*l_2*p_4649280*t_1*l_2*p_2597760*l_1*p_42754965*t_1*l_2*p_2597760*l_1*p_85367641*t_2*l_1*p_1499520*l_2*p_170653269>")
L_N = (g5, h5)

"""
This is the normaliser of a 5A element in the Monster. We claim this particular instance normalises
"""

x5 = MM("M<y_687h*x_0ebfh*d_5fah*p_173070035*l_2*p_1457280*l_1*p_583971*l_2>")
L_E = [x5]

"""
Firstly, verify $x_5$ belongs to the correct conjugacy class using $\chi_\MM$:
"""

x5.order() # 5
x5.in_G_x0() # True
x5.chi_G_x0()[0] # 133

"""
With that settled, show the claimed generators belong to the normaliser of $x_5$.
"""

check_normalise(L_E, L_N) # True

"""
As for showing the entire normaliser is generated, begin by demonstrating that $\langle g_5, h_5 \rangle$ contains the centraliser $5 \times \text{HN}$ of $x_5$.
The presence of the centre $\langle x_5 \rangle \sim 5$ is easily checked:
"""

h5**19 == x5 # True

"""
For the quotient group $\text{HN}$ of the centraliser, consider the following:
"""

x5**(h5**5) == x5 # True
x5**(g5**4) == x5 # True
(g5**4).order() # 11
(h5**5).order() # 19

"""
Since these are elements of the centraliser with orders relatively prime to 5,
they project to elements of order 11 and 19 in the $\text{HN}$. No maximal subgroup
thereof has order divisible by both primes, ensuring the entire $\text{HN}$
is generated. $\langle g_5, h_5 \rangle$ contains the centraliser $5 \times \text{HN}$ of $x_5$.
The presence of the centre $\langle x_5 \rangle \cong 5$ is easily checked:
"""

h5**19 == x5 # True

"""
For the quotient group $\text{HN}$ of the centraliser, consider the following:
"""

x5**(h5**5) == x5 # True
x5**(g5**4) == x5 # True
(g5**4).order() # 11
(h5**5).order() # 19

"""
Since these are elements of the centraliser with orders relatively prime to 5,
they project to elements of order 11 and 19 in the $\text{HN}$. No maximal subgroup
thereof has order divisible by both primes, ensuring the entire $\text{HN}$
is generated.  It then only remains to show $g_5$ conjugates $x_5$ to all its non-trivial powers.
"""

x5**g5 == x5**2 # True

"""
Since 2 is a primitive root modulo 5, the result follows.
"""

"""
## $5^{1+6}{:}2 \udot \J2{:}4$ <a id="norm5B"></a>
The following generators are derived from a set published (without proof) by Dietrich, Lee, and Popiel.

Generators are
"""

g5b = MM("M<y_365h*x_140h*d_86fh*p_65282108*l_1*p_1457280*l_2*p_13039158*t_1*l_1*p_1394880*l_1*p_10666896*l_1*p_151680*t_2*l_1*p_1457280*l_2*p_32007587*l_1*t_2*l_2*p_1943040*l_2*p_43682512*t_1*l_1*p_1457280*l_2*p_16352*t_1*l_1*p_2640000*l_1*p_45296*t_2*l_2*p_2386560*l_2*p_53802531>")
h5b = MM("M<y_515h*x_0e77h*d_6d0h*p_149677978*l_2*p_1457280*l_1*p_1908003*l_2*t_1*l_1*p_1457280*l_2*p_43704570*t_1*l_2*p_2386560*l_2*p_43615141*t_1*l_2*p_2386560*l_2*p_43160081*t_1*l_2*p_2956800*l_1*p_127988769*t_1*l_2*p_1985280*l_1*p_43615109*t_1*l_1*p_1499520*l_2*p_43175446>")
L_N = (g5b, h5b)

"""
This is the normaliser of a 5B element in the Monster. We claim this particular instance normalises
"""

# This is the product of the generators of Dietrich, Lee, and Popiel's - and our! - standard B-type A5.
x5b = MM("M<y_5e2h*x_19e5h*d_180h*p_47732031*l_1*p_2027520*l_1*p_12115667*l_2*t_1*l_2*p_1457280*l_1*p_22333033*l_1*t_1*l_1*p_1920*l_2*p_10668672*l_2*p_10392960*t_1*l_2*p_2386560*l_2*p_53903650*t_2*l_2*p_2830080*l_2*p_106661290*t_1*l_2*p_2597760*l_1*p_43613421*t_2*l_2*p_2830080*l_2*p_96456578>")
L_E = [x5b]

"""
Firstly, verify $x_{5b}$ belongs to the correct conjugacy class using $\chi_\MM$:
"""

# The following element, which appears in Dietrich, Lee, and Popiel, conjugates x_{5b} into G_x0
c = MM("M<y_4f1h*x_9bch*d_0f77h*p_106507260*l_1*p_80762880*l_2*p_213375504*t_2*l_1*p_1499520*l_2*p_583047*t_2*l_2*p_1900800*l_2*p_1040998*t_2*l_2*p_2386560*l_2*p_21331401*t_1>")
x5b_conj = x5b**c

x5b_conj.order() # 5
x5b_conj.in_G_x0() # True
x5b_conj.chi_G_x0()[0] # 8

"""
With that settled, show the claimed generators belong to the normaliser of $x_{5b}$.
"""

check_normalise(L_E, L_N) # True

"""
As for showing the entire normaliser is generated, begin by showing that
$\langle g_{5b}, h_{5b} \rangle$ contains the centraliser $5^{1+6} \udot 2 \udot \text{J}_2$ of $x_{5b}$.
Start with a computation of some element orders in the centraliser.
"""

x5b**g5b == x5b**(h5b**4) == x5b # True
c = g5b*h5b**4
g5b.order() # 70
(h5b**4).order() # 3
c.order() # 5

"""
Considerations of the orders of elements that can lie in the normal subgroup
$5^{1+6} \udot 2$ and in the factor group $\text{J}_2$ prove that
$g_{5b}$ must project to an element of order 7 in the factor group,
$h_{5b}^4$ to an element of order 3, and their product to an element of
order 1 or 5; since two elements of different orders cannot have the identity
as a product, however, only 5 is possible in this last case. No maximal
subgroup of $\text{J}_2$ has order divisible by both 5 and 7, so this proves
all cosets of the normal subgroup $5^{1+6} \udot 2$ are represented in
$\langle g_{5b}, h_{5b} \rangle$.

To finish the centraliser, note that by the above $g_{5b}^7$ lies in $5^{1+4} \udot 2$.
It furthermore has order 10, and thus generates the outer coset of the
$5^{1+6}$ in the subgroup. The normal subgroup $5^{1+6}$ in turn contains
$g_{5b}^7 \left( g_{5b}^7 \right)^{h_{5b}}$ and any products of conjugates thereof
in the normaliser $N \left( x_{5b} \right)$:
"""

y5b = MM("M<y_328h*x_1deah*d_0e94h*p_39050854*l_2*p_960*l_1*p_4080*t_1*l_1*p_3840*l_2*p_24336*l_2*t_1*l_1*p_3840*l_1*p_23376*l_1*p_6548160*t_1*l_2*p_3020160*l_2*t_1*l_2*p_2956800*l_1*p_10784036*t_1*l_1*p_2640000*l_1*p_15392*t_2*l_2*p_2956800*l_1*p_96481545*t_2*l_1*p_1499520*l_2*p_85836106>")
gs = (
    MM("M<y_5aah*x_1044h*d_573h*p_118926544*l_1*p_2999040*l_1*p_10860100*t_2*l_2*p_2956800*l_1*p_12133816*l_1*t_1*l_1*p_960*l_2*p_10666848*l_2*p_2391360*t_1*l_2*p_1457280*l_1*p_576391*t_1*l_1*p_1415040*l_2*p_4128*l_1*p_4331520*t_2*l_2*p_2386560*l_2*p_42710820*t_2*l_1*p_1499520*l_2*p_96460387>"),
    MM("M<y_44h*x_1af9h*d_0ec0h*p_238846774*l_2*p_1900800*l_2*p_2835364*t_1*l_2*p_2787840*l_2*p_22310042*l_1*t_2*l_2*p_1858560*l_1*p_465840*l_2*p_2013120*t_1*l_2*p_2597760*l_1*p_21549732*t_1*l_2*p_1900800*l_2*p_87589*t_1*l_2*p_2597760*l_1*p_42736704*t_2*l_1*p_2027520*l_1*p_78930>")
)
hs = (
    MM("M<y_168h*x_1984h*d_809h*p_50180569*l_1*p_70118400*l_2*p_171684480*l_1*t_2*l_2*p_1900800*l_2*p_465888*l_2*t_1*l_1*p_1393920*l_2*p_465840*l_1*p_4696320*t_1*l_1*p_1499520*l_2*p_64125701*t_2*l_2*p_1393920*l_2*p_466800*l_1*p_2415360*t_1*l_2*p_1920*l_2*p_64016064*t_2*l_2*p_1457280*l_1*p_48132>"),
    MM("M<y_4abh*x_1961h*d_0f8h*p_162877349*l_2*p_1900800*l_2*p_32514568*l_1*t_1*l_1*p_1920*l_1*p_2788176*l_1*t_1*l_1*p_2027520*l_1*p_2815284*l_2*t_2*l_1*p_2640000*l_1*p_13442*t_2*l_1*p_2027520*l_1*p_177067*t_2*l_1*p_1393920*l_1*p_10666848*l_1*p_601920*t_1*l_1*p_8891520*l_1*t_2*l_2*p_1943040*l_2*p_64046821>")
)

l = (g5b**7*(g5b**7)**h5b).reduce()
gens = [l**g5b*(l**2)**(g5b**4), l**(g5b**3)/l**(g5b**4)]

x5b == comm(l, l**g5b)**3 # True
y5b == l**(g5b**2)*gens[1] # True
gs == (gens[0]/gens[1]/x5b**2*(l**2)**g5b*(l**2)**(g5b**2)*(l**2)**(g5b**5), gens[0]**2/gens[1]*x5b**2*l**g5b*(l**2)**(g5b**2)/l**(g5b**5)) # True
hs == (l**3*gens[1]*l**(g5b**5), l**(g5b**5)) # True

"""
They in fact satisfy all the conditions for Lemma 2.2
with $N = 5^{1+6}$ and $\sigma$ as defined below:
"""

σ = MM("M<y_562h*x_184ch*d_94eh*p_131788348*l_1*p_2999040*l_1*p_2388997*t_1*l_2*p_1900800*l_2*p_21860507*l_2*t_1*l_2*p_2830080*l_2*p_2795987*l_1*t_1*l_2*p_2830080*l_2*p_21442979*t_2*l_2*p_2344320*l_2*p_1464512*l_1*t_1*l_1*p_1499520*l_1*p_42716505*t_2*l_2*p_2787840*l_2*p_5776>")
check_lemma_2_2(x5b, y5b, l, gs, hs, σ) # True

"""
We conclude that $x_{5b}$, $y_{5b}$, $\ell$, `gs`, and `hs` generate
$5^{1+6}$. It then only remains to show $h_{5b}$ conjugates $x_{5b}$ to all 4 of
its non-trivial powers.
"""

x5b**h5b == x5b**3 # True

"""
Since 3 is a primitive root modulo 5, the result follows.
"""

"""
## $\left( 5^2{:}4 \udot 2^2 \times \unt{3}{5} \right){:}\sym{3}$ <a id="norm5A2"></a>

Generators for this maximal subgroup are given by
"""

g5a2 = MM("M<y_23bh*x_5beh*d_91ch*p_17762158*l_1*p_74880*l_1*t_2*l_2*p_2787840*l_2*p_32476072*l_1*t_1*l_2*p_2956800*l_1*p_32567542*l_2*t_1*l_2*p_1885440*l_1*t_1*l_2*p_2787840*l_2*p_1905317*t_1*l_2*p_1985280*l_1*p_64001603*t_2*l_2*p_2597760*l_1*p_43152307*t_2*l_2*p_1457280*l_1*p_54939>")
h5a2 = MM("M<y_142h*x_1975h*d_0a9dh*p_114914232*l_2*p_70118400*t_1*l_2*p_1985280*l_1*p_1508727*l_1*t_1*l_1*p_1394880*l_2*p_22320*l_1*p_281280*t_2*l_2*p_1457280*l_1*p_576403*t_1*l_2*p_1393920*l_1*p_10665888*l_1*p_702720*t_2*l_2*p_5664000*l_1*t_1*l_2*p_2956800*l_1*p_42738629>")
L_N = (g5a2, h5a2)

"""
This is the normaliser of a 5A-pure subgroup of $\MM$ with structure $5^2$.
We claim this particular instance normalises the group generated by
"""

x5 = MM("M<y_687h*x_0ebfh*d_5fah*p_173070035*l_2*p_1457280*l_1*p_583971*l_2>")
y5 = MM("M<y_3fdh*x_5f5h*d_9d0h*p_117977088*l_1*p_1499520*l_1*p_85818804*t_2*l_1*p_1457280*l_2*p_945826*t_2*l_2*p_2597760*l_1*p_21361192*t_2*l_2*p_2830080*l_2*p_21358257*t_2*l_2*p_2597760*l_1*p_96483476*t_1*l_2*p_2830080*l_2*p_43151460*t_1*l_2*p_1985280*l_1*p_42728983>")
L_E = (x5, y5)

"""
Note $x_5$ is as in [Theorem 2.12](#norm5A).  
Firstly, verify that $x_5$ and $y_5 \notin \langle x_5 \rangle$ are
commuting elements of order 5:
"""

# x5 was shown to have order 5 in the proof of Theorem 2.12
y5.order() # 5
x5*y5 == y5*x5 # True
y5 in [x5**i for i in range(1, 5)] # False

"""
It follows that $\langle x_5, y_5 \rangle \cong 5^2$.
As for 5A-purity, recall from the proof of [Theorem 2.12](#norm5A) that $x_5 \in \textrm{5A}$.
Since all powers of 5A elements in $\MM$ other than the identity are themselves
5A elements, it thus suffices to conjugate $x_5$ to a generator of each of
the cyclic subgroups of order 5 in $\langle x_5, y_5 \rangle$.
A set of generators (excluding $x_5$, which is already known to lie in 5A)
and of conjugating elements is as follows. Note that all conjugating elements
belong to $\langle g_{5a2}, h_{5a2} \rangle$.
"""

cyclic_gens = [y5] + [x5*y5**i for i in range(1, 5)]
conjugators = [h5a2, g5a2**4, h5a2*g5a2**2*h5a2**2, g5a2**2*h5a2*g5a2, h5a2*g5a2*h5a2**2]
all([x5**conjugators[i] == cyclic_gens[i] for i in range(len(cyclic_gens))]) # True

"""
With that settled, show the claimed generators belong to the normaliser of $\langle x_5, y_5 \rangle$.
"""

map_5_2 = map_to_vectors(L_E)
check_normalise(L_E, L_N, group_set=map_5_2) # True

"""
As for showing the entire normaliser of structure $\left( 5^2{:}4 \udot 2^2 \times \unt{3}{5} \right){:}\sym{3}$ is generated,
begin by verifying that the homomorphism induced
by $\langle g_{5a2}, h_{5a2} \rangle$'s action on $\langle x_5, y_5 \rangle$
has an image of size $\left| 4 \udot 2^2 \right| \left| \sym{3} \right| =
    16 \cdot 6 = 96$:
"""

size_image(L_N, map_5_2, basis=L_E) # 96

"""
It hence suffices to prove that the centraliser $5^2 \times \unt{3}{5}$ is contained
in $\langle g_{5a2}, h_{5a2} \rangle$. The factor $5^2$ is necessarily
$\langle x_5, y_5 \rangle$, with the former generator shown above to be conjugate
to the latter by an element of $\langle g_{5a2}, h_{5a2} \rangle$, so that
for the $5^2$ it suffices to exhibit a word in $g_{5a2}$ and $h_{5a2}$ equal
to $y_5$:
"""

((g5a2*h5a2**2)**2*g5a2)**18 == y5 # True

"""
We claim that the factor $\unt{3}{5}$ is generated by the following two elements.
of $C_\MM \left( \langle x_5, y_5 \rangle \right)$.
"""

x7 = ((g5a2*h5a2)**2*g5a2/(h5a2*g5a2**2*h5a2))**5
x7.order() # 7
x7**x5 == x7**y5 == x7 # True
x8 = (h5a2**2*g5a2*h5a2*g5a2/(g5a2*h5a2*g5a2*h5a2**2))**5
x8.order() # 8
x8**x5 == x8**y5 == x8 # True

"""
Since 7 and 8 are relatively prime to $5^2$,
these elements certainly lie in the factor $\unt{3}{5}$
of the centraliser. Moreover, data in the GAP Character Table
Library show that the only maximal subgroup of $\unt{3}{5}$
with order divisible by both 7 and 8 is $\alt{7}$, which does
not contain elements of order 8, $\unt{3}{5} \le \langle g_{5a2}, h_{5a2} \rangle$
and the proof is complete.
"""

"""
## $5^{2+2+4}{:}\left( \sym{3} \times \ling{2}{5} \right)$ <a id="norm5B2"></a>

Generators for this maximal subgroup are given by
"""

g5b2 = MM("M<y_111h*x_0dd4h*d_74eh*p_5787023*l_1*p_59473920*l_2*p_121566816*t_2*l_1*p_2640000*l_1*p_1504848*l_1*t_2*l_2*p_1943040*l_2*p_12545590*l_2*t_1*l_1*p_1499520*l_2*p_53801586*t_1*l_2*p_2386560*l_2*p_64042024*t_1*l_2*p_1943040*l_2*p_43237049*t_2*l_2*p_2956800*l_1*p_43618929>")
h5b2 = MM("M<y_5d6h*x_459h*d_367h*p_7561418*l_2*p_80762880*l_1*p_129106560*l_2*t_2*l_2*p_78101760*l_1*p_200069808*l_2*t_2*l_1*p_2027520*l_1*p_22330135*l_1*t_2*l_2*p_2787840*l_2*p_10581*t_2*l_1*p_1499520*l_1*p_10717667*t_2*l_2*p_2787840*l_2*p_32968691*l_1*t_1*l_2*p_1985280*l_1*p_42715556*t_2*l_1*p_2027520*l_1*p_57745>")
L_N = (g5b2, h5b2)

"""
Maximal subgroups of the given structure are the normalisers of
certain 5B-pure subgroup of $\MM$ with structure $5^2$. We claim this particular instance
normalises $\langle x_{5b}, y_{5b} \rangle$, where $x_{5b}$ and $y_{5b}$
are as in [Theorem 2.13](#norm5B):
"""

x5b = MM("M<y_5e2h*x_19e5h*d_180h*p_47732031*l_1*p_2027520*l_1*p_12115667*l_2*t_1*l_2*p_1457280*l_1*p_22333033*l_1*t_1*l_1*p_1920*l_2*p_10668672*l_2*p_10392960*t_1*l_2*p_2386560*l_2*p_53903650*t_2*l_2*p_2830080*l_2*p_106661290*t_1*l_2*p_2597760*l_1*p_43613421*t_2*l_2*p_2830080*l_2*p_96456578>")
y5b = MM("M<y_328h*x_1deah*d_0e94h*p_39050854*l_2*p_960*l_1*p_4080*t_1*l_1*p_3840*l_2*p_24336*l_2*t_1*l_1*p_3840*l_1*p_23376*l_1*p_6548160*t_1*l_2*p_3020160*l_2*t_1*l_2*p_2956800*l_1*p_10784036*t_1*l_1*p_2640000*l_1*p_15392*t_2*l_2*p_2956800*l_1*p_96481545*t_2*l_1*p_1499520*l_2*p_85836106>")
L_E = (x5b, y5b)

"""
The proof of [Theorem 2.13](#norm5B) showed not only that
$y_{5b} \notin \langle x_{5b} \rangle$ is an element of order 5 commuting
with the 5B element $x_{5b}$, so that they certainly generate a group $5^2$,
but also that $y_{5b} \in 5^{1+6} < 5^{1+6}{:}2 \udot \J2{:}4$. According to Wilson's
odd local paper, there are precisely two conjugacy classes of
$5^2 \le 5^{1+6}$ containing the centre in a 5B normaliser, with one class
(centraliser $\left( 5 \times 5^{1+4} \right){:}5^2{:}\sym{3}$) having
as a normaliser the desired maximal subgroup of $\MM$ and
the other (centraliser $5 \times 5^{1+4}{:}2^{1+4}{:}5$) not. It
thus suffices to demonstrate $\langle x_{5b}, y_{5b} \rangle$ is centralised
by an element of order 3.
"""

t = MM("M<y_398h*x_1031h*d_6f5h*p_167269163*l_1*p_464640*l_2*p_1394160*l_2*t_1*l_2*p_2787840*l_2*p_2354472*l_2*t_1*l_2*p_1985280*l_1*p_21817286*l_2*t_2*l_2*p_2597760*l_1*p_10702241*t_2*l_2*p_2956800*l_1*p_85332884*t_1*l_1*p_1499520*l_1*p_43678701*t_1*l_1*p_1499520*l_2*p_53881527>")

t.order() # 3
x5b*t == t*x5b # True
y5b*t == t*y5b # True

"""
With that settled, show the claimed generators belong to the normaliser of $\langle x_{5b}, y_{5b} \rangle$.
"""

map_5_2 = map_to_vectors(L_E)
check_normalise(L_E, L_N, group_set=map_5_2) # True

"""
As for showing the entire normaliser of structure $5^{2+2+4}{:}\left( \sym{3} \times \ling{2}{5} \right)$ is generated,
begin by verifying that the homomorphism induced
by $\langle g_{5b2}, h_{5b2} \rangle$'s action on $\langle x_{5b}, y_{5b} \rangle$
has an image of size $\left| \ling{2}{5} \right| = \left( 5^2 - 1 \right)
    \left( 5^2 - 5 \right) = 480$:
"""

size_image(L_N, map_5_2, basis=L_E) # 480

"""
It thus suffices to prove that the centraliser
$\left( 5 \times 5^{1+4} \right){:}5^2{:}\sym{3}$ lies
in $\langle g_{5b2}, h_{5b2} \rangle$. For the 5-group of order
$5^{1+1+4+2} = 5^8$, recall from the proof of [Theorem 2.13](#norm5B) that
$x_{5b}$, $y_{5b}$, and certain elements $\ell, \left\{ g_i \right\}_{i=1}^2,
    \left\{ h_i \right\}_{i=1}^2, \sigma$ satisfy the conditions of
Lemma 2.2 with $p = 5$ and $k = 2$. The elements $x_{5b}, y_{5b}, g_i, h_i, h_i^{\sigma}$
therefore generate a 5-group lying in $\cma{x_{5b}, y_{5b}}$ of order at least $5^8$,
so that it is enough to exhibit words for them in $g_{5b2}, h_{5b2}$.
"""

# The aforementioned elements
gs = (
    MM("M<y_5aah*x_1044h*d_573h*p_118926544*l_1*p_2999040*l_1*p_10860100*t_2*l_2*p_2956800*l_1*p_12133816*l_1*t_1*l_1*p_960*l_2*p_10666848*l_2*p_2391360*t_1*l_2*p_1457280*l_1*p_576391*t_1*l_1*p_1415040*l_2*p_4128*l_1*p_4331520*t_2*l_2*p_2386560*l_2*p_42710820*t_2*l_1*p_1499520*l_2*p_96460387>"),
    MM("M<y_44h*x_1af9h*d_0ec0h*p_238846774*l_2*p_1900800*l_2*p_2835364*t_1*l_2*p_2787840*l_2*p_22310042*l_1*t_2*l_2*p_1858560*l_1*p_465840*l_2*p_2013120*t_1*l_2*p_2597760*l_1*p_21549732*t_1*l_2*p_1900800*l_2*p_87589*t_1*l_2*p_2597760*l_1*p_42736704*t_2*l_1*p_2027520*l_1*p_78930>")
)
hs = (
    MM("M<y_168h*x_1984h*d_809h*p_50180569*l_1*p_70118400*l_2*p_171684480*l_1*t_2*l_2*p_1900800*l_2*p_465888*l_2*t_1*l_1*p_1393920*l_2*p_465840*l_1*p_4696320*t_1*l_1*p_1499520*l_2*p_64125701*t_2*l_2*p_1393920*l_2*p_466800*l_1*p_2415360*t_1*l_2*p_1920*l_2*p_64016064*t_2*l_2*p_1457280*l_1*p_48132>"),
    MM("M<y_4abh*x_1961h*d_0f8h*p_162877349*l_2*p_1900800*l_2*p_32514568*l_1*t_1*l_1*p_1920*l_1*p_2788176*l_1*t_1*l_1*p_2027520*l_1*p_2815284*l_2*t_2*l_1*p_2640000*l_1*p_13442*t_2*l_1*p_2027520*l_1*p_177067*t_2*l_1*p_1393920*l_1*p_10666848*l_1*p_601920*t_1*l_1*p_8891520*l_1*t_2*l_2*p_1943040*l_2*p_64046821>")
)
σ = MM("M<y_562h*x_184ch*d_94eh*p_131788348*l_1*p_2999040*l_1*p_2388997*t_1*l_2*p_1900800*l_2*p_21860507*l_2*t_1*l_2*p_2830080*l_2*p_2795987*l_1*t_1*l_2*p_2830080*l_2*p_21442979*t_2*l_2*p_2344320*l_2*p_1464512*l_1*t_1*l_1*p_1499520*l_1*p_42716505*t_2*l_2*p_2787840*l_2*p_5776>")

T = [comm(1/h5b2, g5b2**-2), comm(1/(g5b2*h5b2), g5b2**-2), comm(h5b2**-2, g5b2**-2), comm(1/h5b2, g5b2**-2/h5b2), h5b2**6/g5b2**2]
T += [comm(1/(g5b2**2*h5b2), g5b2**-2), g5b2*h5b2**2*g5b2**2/(g5b2*h5b2*g5b2**2*h5b2), comm(1/(h5b2*g5b2*h5b2), g5b2**-2)]
U = [T[0]*T[5]**3, T[2]/(T[4]**4/T[5]**4*T[6]*T[1]**4), T[3]/(T[4]**4/T[5]*T[6]*T[1]**4), T[7]/(T[6]**2*T[1]**4)]

x5b == U[1]*U[0]/U[3] # True
y5b == U[0]**3/U[1]*U[2]**3 # True
gs[0] == U[3]**3/U[1] # True
gs[1] == U[1]**3*U[2]**2*U[3]**3 # True
hs[0] == (U[3]**-2/U[2]**3/U[1]/U[0]*T[5]**2*T[4]*T[6]**2/(U[1]*U[3]*T[1])**3)**3 # True
hs[1] == U[3]**2*U[0]**2/(U[1]**2*T[5]) # True
hs[0]**σ == (U[2]/T[5]/U[3]**3*T[4]**2*T[6]/T[1])**3 # True
hs[1]**σ == U[1]*U[3]*T[1] # True

"""
The factor group $\sym{3}$ is in turn generated by any elements
of order 2 and 3. Since these are coprime to $5^8$, we need only
exhibit elements of these orders in $\langle g_{5b2}, h_{5b2} \rangle \cap
    \cma{x_{5b}, y_{5b}}$ to complete the proof.
"""

u = (g5b2*h5b2)**2*g5b2**3*h5b2**2*g5b2/(h5b2*g5b2**2*h5b2**3*g5b2*h5b2)
x5b*u == u*x5b # True
y5b*u == u*y5b # True
u.order() # 2

v = h5b2*g5b2*h5b2**5*g5b2*h5b2/(g5b2**5*h5b2*g5b2**3)
x5b*v == v*x5b # True
y5b*v == v*y5b # True
v.order() # 3

"""
## $5^{3+3} \udot \left( 2 \times \psl{3}{5} \right)$ <a id="norm5B3"></a>

Generators for this maximal subgroup are given by
"""

g5b3 = MM("M<y_4dch*x_13fh*d_377h*p_149972229*l_2*p_68344320*l_1*p_127776192*t_2*l_1*p_69674880*l_2*p_131767728*l_1*t_2*l_1*p_1499520*l_2*p_13016282*l_2*t_1*l_2*p_1457280*l_1*p_1026658*t_2*l_1*p_1499520*l_1*p_21375574*t_1*l_2*p_2597760*l_1*p_64036432*t_1*l_2*p_2597760*l_1*p_42833875>")
h5b3 = MM("M<y_46bh*x_0dc3h*d_772h*p_54616187*l_1*p_79875840*l_1*p_182772480*l_1*t_2*l_2*p_70118400*l_2*p_241760688*l_2*t_2*l_1*p_1499520*l_2*p_32512631*l_2*t_2*l_1*p_1499520*l_2*p_10690766*t_2*l_2*p_1985280*l_1*p_85373291*t_1*l_2*p_2830080*l_2*p_21337121*t_2*l_2*p_937920*l_1>")
L_N = (g5b3, h5b3)

"""
Maximal subgroups of the given structure are the normalisers of
certain 5B-pure subgroup of $\MM$ with structure $5^3$. We claim this particular instance
normalises $\langle x_{5b}, y_{5b}, g_2 \rangle$, where all generators
are as in the proof of [Theorem 2.13](#norm5B)
"""

x5b = MM("M<y_5e2h*x_19e5h*d_180h*p_47732031*l_1*p_2027520*l_1*p_12115667*l_2*t_1*l_2*p_1457280*l_1*p_22333033*l_1*t_1*l_1*p_1920*l_2*p_10668672*l_2*p_10392960*t_1*l_2*p_2386560*l_2*p_53903650*t_2*l_2*p_2830080*l_2*p_106661290*t_1*l_2*p_2597760*l_1*p_43613421*t_2*l_2*p_2830080*l_2*p_96456578>")
y5b = MM("M<y_328h*x_1deah*d_0e94h*p_39050854*l_2*p_960*l_1*p_4080*t_1*l_1*p_3840*l_2*p_24336*l_2*t_1*l_1*p_3840*l_1*p_23376*l_1*p_6548160*t_1*l_2*p_3020160*l_2*t_1*l_2*p_2956800*l_1*p_10784036*t_1*l_1*p_2640000*l_1*p_15392*t_2*l_2*p_2956800*l_1*p_96481545*t_2*l_1*p_1499520*l_2*p_85836106>")
gs = (
    MM("M<y_5aah*x_1044h*d_573h*p_118926544*l_1*p_2999040*l_1*p_10860100*t_2*l_2*p_2956800*l_1*p_12133816*l_1*t_1*l_1*p_960*l_2*p_10666848*l_2*p_2391360*t_1*l_2*p_1457280*l_1*p_576391*t_1*l_1*p_1415040*l_2*p_4128*l_1*p_4331520*t_2*l_2*p_2386560*l_2*p_42710820*t_2*l_1*p_1499520*l_2*p_96460387>"),
    MM("M<y_44h*x_1af9h*d_0ec0h*p_238846774*l_2*p_1900800*l_2*p_2835364*t_1*l_2*p_2787840*l_2*p_22310042*l_1*t_2*l_2*p_1858560*l_1*p_465840*l_2*p_2013120*t_1*l_2*p_2597760*l_1*p_21549732*t_1*l_2*p_1900800*l_2*p_87589*t_1*l_2*p_2597760*l_1*p_42736704*t_2*l_1*p_2027520*l_1*p_78930>")
)
L_E = (x5b, y5b, gs[1])

"""
This group is certainly an elementary abelian 5-group --- as shown
in proving [Theorem 2.13](#norm5B), the elements $x_{5b}, y_{5b}, g_2 \in
    \cma{x_{5b}, y_{5b}}$ all have order 5 --- and hence has a 5-local subgroup
of $\MM$ as a normaliser. On the other hand, Wilson proves in his odd local paper
that all such subgroups lie in a maximal subgroup of $\MM$ with shape
$5^{1+6}{:}2 \udot \J2{:}4$, $5^{1+6}{:}2 \udot \J2{:}4^2$, $5^{1+6}{:}2 \udot \J2{:}4^3$, or $5^{1+6}{:}2 \udot \J2{:}4^4$; since only the third of these
has order divisible by 31, $\nma{x_{5b}, y_{5b}, g_2}$ must lie inside
the desired subgroup of $\MM$ if it is normalised by an element of order 31.
"""

map_5_3 = map_to_vectors(L_E)
check_normalise(L_E, L_N, group_set=map_5_3) # True
(h5b3**2).order() # 31

"""
This incidentally establishes that the claimed generators belong
to the normaliser of $\langle x_{5b}, y_{5b}, g_2 \rangle$.

It will follow that $g_{5b3}, h_{5b3}$ generate the entire subgroup of
structure $5^{3+3} \udot \left( 2 \times \psl{3}{5} \right)$ upon showing that the former group has order
$\left| 5^{3+3} \udot \left( 2 \times \psl{3}{5} \right) \right| = 5^6 \cdot 2 \left| \psl{3}{5} \right|$.
First verify that the homomorphism induced
by $\langle g_{5b3}, h_{5b3} \rangle$'s action on $\langle x_{5b}, y_{5b}, g_2 \rangle$
has an image of size $\left| \lins{3}{5} \right| = \left( 5^3 - 1 \right)
    \left( 5^3 - 5 \right) \left( 5^3 - 5^2 \right)/\left( 5 - 1 \right) = 372000$:
"""

size_image(L_N, map_5_3, basis=L_E) # 372000

"""
It thus suffices to confirm that $\left| \cma{x_{5b}, y_{5b}, g_2} \cap
    \langle g_{5b3}, h_{5b3} \rangle \right| \ge 5^6 \cdot 2$.
Lemma 2.2 applied to $x_{5b}$, $y_{5b}$, and the elements
$\ell, \left\{ g_i \right\}_{i=1}^2, \left\{ h_i \right\}_{i=1}^2, \sigma$
defined in the proof of [Theorem 2.13](#norm5B) provides a way to exhibit
a 5-group of order at least $5^6$:
"""

# The elements mentioned
hs = (
    MM("M<y_168h*x_1984h*d_809h*p_50180569*l_1*p_70118400*l_2*p_171684480*l_1*t_2*l_2*p_1900800*l_2*p_465888*l_2*t_1*l_1*p_1393920*l_2*p_465840*l_1*p_4696320*t_1*l_1*p_1499520*l_2*p_64125701*t_2*l_2*p_1393920*l_2*p_466800*l_1*p_2415360*t_1*l_2*p_1920*l_2*p_64016064*t_2*l_2*p_1457280*l_1*p_48132>"),
    MM("M<y_4abh*x_1961h*d_0f8h*p_162877349*l_2*p_1900800*l_2*p_32514568*l_1*t_1*l_1*p_1920*l_1*p_2788176*l_1*t_1*l_1*p_2027520*l_1*p_2815284*l_2*t_2*l_1*p_2640000*l_1*p_13442*t_2*l_1*p_2027520*l_1*p_177067*t_2*l_1*p_1393920*l_1*p_10666848*l_1*p_601920*t_1*l_1*p_8891520*l_1*t_2*l_2*p_1943040*l_2*p_64046821>")
)
σ = MM("M<y_562h*x_184ch*d_94eh*p_131788348*l_1*p_2999040*l_1*p_2388997*t_1*l_2*p_1900800*l_2*p_21860507*l_2*t_1*l_2*p_2830080*l_2*p_2795987*l_1*t_1*l_2*p_2830080*l_2*p_21442979*t_2*l_2*p_2344320*l_2*p_1464512*l_1*t_1*l_1*p_1499520*l_1*p_42716505*t_2*l_2*p_2787840*l_2*p_5776>")

x = ((h5b3*g5b3**2)**3).reduce()
T = [x, x**(1/g5b3), x**(1/h5b3), x**(1/g5b3)/x**(1/g5b3**2), x**(1/(g5b3*h5b3)), x**(1/(h5b3*g5b3)), x**(1/h5b3**2)]

# All the elements that will be exhibited were required to commute with x5b, y5b
# by the hypotheses of the lemma, so only the interaction with gs[1] remains
# to be checked.
all(gs[1]*g == g*gs[1] for g in T) # True

U = [T[1]*T[0], T[2]*T[0], T[4]*T[0]/T[3]**3, T[5]*T[0]/T[3], T[6]*T[0]/T[3]**2]

x5b == comm(U[3], U[4])**3 # True
y5b == U[0]/U[2] # True
gs[0] == 1/x5b*U[0]*U[1]**3*U[3]*U[4] # True
gs[1] == U[0]**2*U[1]*U[2] # True
hs[0] == x5b**2*U[0]**2/U[3] # True
hs[0]**σ == x5b*U[0]**2/U[2]**2/T[0]/T[5] # True

"""
Taking these 6 elements as $S$ yields a suitable 5-group
$\langle S \rangle$.

The final factor of 2 in the order may be addressed
by exhibiting an element of order 2 commuting with
$x_{5b}, y_{5b}, g_2$. Such an element certainly cannot lie
in the 5-group above, and hence by Lemma 2.1 extends the group
found so far to one at least twice as large.
"""

(T[0]**5).order() # 2
# Each T[i] commutes with gs[1] by the above
x5b*T[0] == T[0]*x5b # True
y5b*T[0] == T[0]*y5b # True

"""
## $5^4{:}\left( 3 \times 2 \udot \psl{2}{25} \right){:}2$ <a id="norm5B4"></a>

Generators for this maximal subgroup are given by
"""

g5b4 = MM("M<y_585h*x_6f5h*d_0c09h*p_230461632*l_1*p_2027520*l_1*p_23244133*l_2*t_1*l_1*p_1499520*l_1*p_22754355*t_1*l_2*p_2956800*l_1*p_64024725*t_2*l_2*p_2956800*l_1*p_33402704*t_2*l_2*p_2597760*l_1*p_43154328*t_1*l_2*p_2597760*l_1*p_21418932*t_1*l_2*p_1985280*l_1*p_42710800>")
h5b4 = MM("M<y_0feh*x_10f6h*d_0f76h*p_164821028*l_1*p_2640000*l_1*p_10675264*t_2*l_2*p_2597760*l_1*p_663931*t_2*l_2*p_2386560*l_2*p_53820907*t_2*l_2*p_1900800*l_2*p_64576*t_1*l_2*p_1943040*l_2*p_43598792*t_1*l_1*p_1499520*l_2*p_43154325*t_1*l_2*p_2597760*l_1*p_64007368>")
L_N = (g5b4, h5b4)

"""
Maximal subgroups of the given structure are the normalisers of
certain 5B-pure subgroup of $\MM$ with structure $5^4$. We claim this particular instance
normalises the group generated by
"""

x5b = MM("M<y_5e2h*x_19e5h*d_180h*p_47732031*l_1*p_2027520*l_1*p_12115667*l_2*t_1*l_2*p_1457280*l_1*p_22333033*l_1*t_1*l_1*p_1920*l_2*p_10668672*l_2*p_10392960*t_1*l_2*p_2386560*l_2*p_53903650*t_2*l_2*p_2830080*l_2*p_106661290*t_1*l_2*p_2597760*l_1*p_43613421*t_2*l_2*p_2830080*l_2*p_96456578>")
y5b = MM("M<y_328h*x_1deah*d_0e94h*p_39050854*l_2*p_960*l_1*p_4080*t_1*l_1*p_3840*l_2*p_24336*l_2*t_1*l_1*p_3840*l_1*p_23376*l_1*p_6548160*t_1*l_2*p_3020160*l_2*t_1*l_2*p_2956800*l_1*p_10784036*t_1*l_1*p_2640000*l_1*p_15392*t_2*l_2*p_2956800*l_1*p_96481545*t_2*l_1*p_1499520*l_2*p_85836106>")
a = MM("M<y_488h*x_1667h*d_50ah*p_166845182*l_2*p_23040*l_2*p_32990832*l_2*t_2*l_2*p_2386560*l_2*p_23241248*l_1*t_1*l_2*p_960*l_2*p_1200*l_2*p_6126720*t_1*l_2*p_1457280*l_1*p_1058307*t_1*l_1*p_1393920*l_2*p_21456*l_1*p_763200*t_2*l_2*p_2956800*l_1*p_42714640*t_1*l_2*p_2830080*l_2*p_85815923>")
b = MM("M<y_23h*x_15adh*d_8cfh*p_127564641*l_2*p_2386560*l_2*p_32000867*l_1*t_2*l_2*p_1943040*l_2*p_67351*t_1*l_1*p_2027520*l_1*p_78870*t_1*l_1*p_2640000*l_1*p_42852*t_2*l_2*p_2597760*l_1*p_21861478*l_1*t_2*l_2*p_2956800*l_1*p_53436210*t_1*l_2*p_2956800*l_1*p_42795380>")
L_E = (x5b, y5b, a, b)

"""
Note $x_{5b}$ and $y_{5b}$ are as in the proof of [Theorem 2.13](#norm5B).
First check that this is an elementary abelian 5-group.
"""

# It has previously been shown x5b, y5b are commuting elements of order 5
a.order() # 5
b.order() # 5
x5b*a == a*x5b # True
y5b*a == a*y5b # True
x5b*b == b*x5b # True
y5b*b == b*y5b # True
a*b == b*a # True

"""
It therefore has a 5-local subgroup of $\MM$ for a normaliser, which by Wilson
must lie in a maximal subgroup of $\MM$ with structure $5^{1+6}{:}2 \udot \J2{:}4$, $5^{1+6}{:}2 \udot \J2{:}4^2$,
$5^{1+6}{:}2 \udot \J2{:}4^3$, or $5^{1+6}{:}2 \udot \J2{:}4^4$. Since only the last of these has order divisible
by 13, exhibiting $x \in \nma{x_{5b}, y_{5b}, a, b}$ of order 13 proves
this normaliser is situated inside a maximal subgroup of the desired structure.
"""

map_5_4 = map_to_vectors(L_E)
check_normalise(L_E, L_N, group_set=map_5_4) # True
(comm(g5b4, h5b4)**6).order() # 13

"""
This incidentally establishes that the claimed generators belong
to the normaliser of $\langle x_{5b}, y_{5b}, a, b \rangle$.

It will follow that $g_{5b4}, h_{5b4}$ generate the entire subgroup of
shape $5^4{:}\left( 3 \times 2 \udot \psl{2}{25} \right){:}2$ upon showing that the former group has order
$\left| 5^4{:}\left( 3 \times 2 \udot \psl{2}{25} \right){:}2 \right| = 5^4 \cdot 3 \cdot 2 \left| \psl{2}{25} \right|
    \cdot 2$. Begin by checking the homomorphism induced
by $\langle g_{5b4}, h_{5b4} \rangle$'s action
on $\langle x_{5b}, y_{5b}, a, b \rangle$ has an image of size
$3 \cdot 2 \left| \psl{2}{25} \right| \cdot 2 = 12 \left( 25^2 - 1 \right)
    \left( 25^2 - 25 \right)/\left( 2 \left( 25 - 1 \right) \right) = 93600$:
"""

size_image(L_N, map_5_4, basis=L_E) # 93600

"""
It thus suffices to confirm that $\left| \cma{x_{5b}, y_{5b}, a, b} \cap
    \langle g_{5b4}, h_{5b4} \rangle \right| \ge 5^4$. Demonstrate
that $x_{5b}, y_{5b}, a, b$ are elements of $\langle g_{5b4}, h_{5b4} \rangle$
and that the group they generate --- enumerated in `map_5_4` above ---
has the desired order.
"""

x5b == comm(h5b4**-2, g5b4**4)**3 # True
y5b == x5b*comm(g5b4**4, h5b4**-2)**(1/g5b4) # True
a == comm(1/h5b4, g5b4**4) # True
b == g5b4*h5b4*g5b4**4/h5b4*g5b4**3 # True

len(map_5_4) # 625

"""
## $\left( 7{:}3 \times \HE \right){:}2$ <a id="norm7A"></a>
Generators are
"""

g7 = MM("M<y_0e5h*x_541h*d_216h*p_10791589*l_2*p_1943040*l_2*p_1045810*t_2*l_2*p_486720*t_2*l_2*p_2830080*l_2*p_64016091*t_1*l_1*p_1457280*l_2*p_574389>")
h7 = MM("M<y_357h*x_0bffh*d_64eh*p_77082512*l_1*p_1499520*l_2*p_1904176*l_2*t_2*l_2*p_1394880*l_2*p_4128*l_1*p_1671360>")
L_N = (g7, h7)

"""
This is the normaliser of a 7A element in the Monster. We claim this particular instance normalises
"""

x7 = MM("M<y_2dh*x_1ecdh*d_0a6bh*p_137531918*l_1*p_2880*l_2*p_21408*l_2*p_662400>")
L_E = [x7]

"""
Firstly, verify $x_7$ belongs to the correct conjugacy class using $\chi_\MM$:
"""

x7.order() # 7
x7.in_G_x0() # True
x7.chi_G_x0()[0] # 50

"""
With that settled, show the claimed generators belong to the normaliser of $x_7$.
"""

check_normalise(L_E, L_N) # True

"""
As for showing the entire normaliser is generated, begin by showing that$\langle g_7, h_7 \rangle$ contains the centraliser $7 \times \text{He}$ of $x_7$.
The presence of the centre $\langle x_7 \rangle \sim 7$ is easily checked:
"""

h7**85 == x7 # True

"""
For the quotient group $\text{He}$ of the centraliser, consider the following:
"""

x7**(g7**6) == x7 # True
x7**(h7**7) == x7 # True
(g7**6).order() # 7
(h7**7).order() # 17
g7**6 in [x7**i for i in range(1, 7)] # False

"""
Since $g_7$ is an element of the centraliser of $x_7$ with order 7 not in the centre 7 thereof
and $h_7$ is such an element with order relatively prime to 7,
they project to elements of order 7 and 17 in the $\text{He}$. No maximal subgroup
thereof has order divisible by both primes, ensuring the entire $\text{He}$
is generated.

It then only remains to show $g_7$ conjugates $x_7$
to all its non-trivial powers.
"""

x7**g7 == x7**3 # True

"""
Since 3 is a primitive root modulo 7, the result follows.
"""

"""
## $7^{1+4}{:}\left( 3 \times 2.\sym{7} \right)$ <a id="norm7B"></a>
The following generators are derived from a set published (without proof) by Dietrich, Lee, and Popiel.

Generators are
"""

g7b = MM("M<y_4eah*x_1f63h*d_4adh*p_227082898*l_2*p_2386560*l_2*p_53835316*t_1*l_2*p_1415040*l_1*p_23280*l_1*t_2*l_1*p_2640000*l_1*p_23218036*l_2*t_1*l_1*p_2640000*l_1*p_11562*t_1*l_2*p_3840*l_2*p_43169760*t_1*l_2*p_2956800*l_1*p_2795179*l_1*t_1*l_1*p_2027520*l_1*p_7697*t_2*l_2*p_3720960*l_1>")
h7b = MM("M<y_735h*x_10f2h*d_0c0h*p_237789565*l_1*p_23040*l_1*p_2112*l_1*t_2*l_1*p_1499520*l_1*p_45266*t_1*l_1*p_1457280*l_2*p_70230*t_1*l_2*p_2830080*l_2*p_12992119*t_2*l_2*p_2386560*l_2*p_106664178*t_2*l_2*p_1457280*l_1*p_500368*t_2*l_2*p_2956800*l_1*p_42717430>")
L_N = (g7b, h7b)

"""
This is the normaliser of a 7B element in the Monster. We claim this particular instance normalises
"""

x7b = MM("M<y_5d3h*x_0a6dh*d_8d4h*p_111142481*l_1*p_2999040*l_1*p_43234193>")
L_E = [x7b]

"""
Firstly, verify $x_{7b}$ belongs to the correct conjugacy class using $\chi_\MM$:
"""

x7b.order() # 7
x7b.in_G_x0() # True
x7b.chi_G_x0()[0] # 1

"""
With that settled, show the claimed generators belong to the normaliser of $x_{7b}$.
"""

check_normalise(L_E, L_N) # True

"""
As for showing the entire normaliser is generated, first define
the following elements. Note that they are all conjugates,
or products of conjugates, of $g_{7b}$ in $\langle g_{7b}, h_{7b} \rangle$.
"""

a0 = g7b**6
a1 = a0**h7b
a2 = a1*a1**h7b
a3 = a0**3/a1**2/a1**(h7b**2)/a1**h7b

"""
We begin by exhibiting a subgroup of order $10080 = \left| 2.\sym{7} \right|$
and $t \in \langle g_{7b}, h_{7b} \rangle$ of order 3 which centralises, but
does not lie in, the subgroup.
"""

y6 = 1/a3*g7b
t = (y6*h7b)**14

t.order() # 3
t*y6 == y6*t # True
t*h7b == h7b*t # True

# For speed, use the fact that the centre of 2S7 is a 2B involution to conjugate the subgroup into G_x0
conjugator = MM("M<y_505h*x_982h*d_55bh*p_26759361*l_2*p_2597760*l_1*p_32070374*l_2*t_1*l_2*p_2830080*l_2*p_22758208*l_1*t_1*l_2*p_1394880*l_1*p_10666896*l_2*p_73920*t_1*l_2*p_2956800*l_1*p_64081477*t_1*l_2*p_1900800*l_2*p_85416579*l_1*p_1858560*t_2*l_1*p_2999040*l_1*p_10686964>")
subgroup_mod_3 = size_image(((y6*t)**conjugator, h7b**conjugator), as_int, set)

len(subgroup_mod_3) # 10080
as_int(t**conjugator) in subgroup_mod_3 # False

"""
It follows that $\langle t, y_6, h_{7b} \rangle$ contains $3 \cdot 10080$ elements, or one
for each coset in the factor group $3 \times 2\sym{7}$ of $7^{1+4}{:}\left( 3 \times 2.\sym{7} \right)$. This group therefore
either contains a representative of each coset or has non-trivial intersection
with the normal subgroup $7^{1+4}$. If the latter holds, the intersection must have order
a power of 7, so that the projection of $\langle t, y_6, h_{7b} \rangle$ to the factor group
has order dividing $3 \cdot 10080 / 7 = 3 \cdot 1440$. But $7 \not\mid 1440$ is prime,
meaning all elements of order 7 in $\langle t, y_6, h_{7b} \rangle$ would lie in
the normal subgroup $7^{1+4}$ and project to the identity in $3 \times 2\sym{7}$.
With this in mind, observe the following:
"""

r7 = (y6*h7b)**6
r7.order() # 7
(r7/h7b).order() # 20
h7b.order() # 6

"""
The fact that 20 and 6 are coprime to $7^5$ implies $r_7 h_{7b}^{-1}$
and $h_{7b}$ project to elements of those same orders modulo the $7^{1+4}$,
and hence that $r_7 = r_7 h_{7b}^{-1} h_{7b}$ does not project to the identity.
This proves $\langle t, y_6, h_{7b}$ contains a representative of each
coset of the normal subgroup $7^{1+4}$ in $7^{1+4}{:}\left( 3 \times 2.\sym{7} \right)$ and intersects that
subgroup trivially.

To finish, it must be verified that $g_{7b}$ and $h_{7b}$ generate
the normal subgroup $7^{1+4}$ of $\nma{x_{7b}}$. Look at the order of $g_{7b}$.
"""

g7b.order() # 42

"""
If $g_{7b}^6$ did not lie in the normal subgroup,
then $g_{7b}$ would necessarily project to an element
of order 42 in the factor group $3 \times 2\sym{7}$.
Since there are no elements of order 42 in $2\sym{7}$,
its 14^th power must be one of the two central elements
of order 3. On the other hand, $t$ above projects
to a central element of order 3 also; it follows that
one of $g_{7b}^{14} t^{-1}$ and $g_{7b}^{14} t^{-2}$ lies
in the normal subgroup:
"""

(g7b**14/t).order() # 21
(g7b**14/t**2).order() # 21

"""
A contradiction follows, so that $g_{7b}^6$ does in fact belong
to the normal subgroup $7^{1+4}$. Its conjugates in $7^{1+4}{:}\left( 3 \times 2.\sym{7} \right)$ thus do too,
so that the elements $a_0$ through $a_3$ defined above likewise belong,
as do the following families of elements:
"""

a0 == MM("M<y_3c4h*x_1c6bh*d_225h*p_238190910*l_2*p_22080*l_1*p_21456*t_2*l_2*p_2344320*l_2*p_22307972*l_2*t_1*l_1*p_2640000*l_1*p_2413941*l_1*t_1*l_2*p_2830080*l_2*p_85332882*t_2*l_1*p_1499520*l_1*p_85414673*t_1*l_2*p_2597760*l_1*p_85814004*l_1*p_21333120*t_1*l_2*p_2830080*l_2*p_22304977*l_1>") # True
a3 == MM("M<y_0a1h*x_29fh*d_115h*p_52081919*l_1*p_1457280*l_2*p_32504931*l_2*t_2*l_2*p_1900800*l_2*p_474338*l_2*t_1*l_1*p_2640000*l_1*p_21801761*l_1*t_1*l_2*p_2386560*l_2*p_64088184*t_1*l_1*p_2880*l_2*p_10666896*l_2*p_4290240*t_2*l_1*p_1499520*l_1*p_106664201*t_2*l_2*p_1943040*l_2*p_86279607>") # True
gs = [MM("M<y_714h*x_0fbch*d_680h*p_104733485*l_1*p_3840*l_2*p_22746528*t_2*l_1*p_2640000*l_1*p_12106888*l_1*t_2*l_2*p_3840*l_2*p_10666752*l_2*p_150720*t_2*l_1*p_1457280*l_2*p_934274*t_2*l_2*p_1985280*l_1*p_64045846*t_1*l_1*p_2999040*l_1*p_495478*t_2*l_2*p_2830080*l_2*p_43260121>")]
hs = [MM("M<y_24h*x_15d3h*d_6bdh*p_221822572*l_2*p_2787840*l_2*p_32130697*l_1*t_1*l_2*p_2597760*l_1*p_10672403*l_2*t_1*l_2*p_1985280*l_1*p_32071298*l_2*t_2*l_2*p_1457280*l_1*p_1483638*t_1*l_2*p_1985280*l_1*p_86258530*t_1*l_2*p_2956800*l_1*p_42671270*t_1*l_2*p_2597760*l_1*p_21338020>")]

l = a0
x7b == comm(a0, a1) # True
gs == [(a0**4*a1**3*a2)**-2] # True
hs == [a0*a1] # True

"""
They in fact satisfy all the conditions for Lemma 2.2
with $y = a_3$, $N = 7^{1+4}$ and $\sigma$ as defined below:
"""

σ = MM("M<y_355h*x_0df5h*d_0af9h*p_129634698*l_1*p_1858560*l_2*p_4032*l_1*p_10292160*t_2*l_2*p_1858560*l_2*p_33434352*l_2*t_2*l_1*p_1457280*l_2*p_12175332*l_2*t_1*l_2*p_2344320*l_2*p_10566*t_1*l_1*p_2640000*l_1*p_50065*t_2*l_2*p_2597760*l_1*p_21893138*l_1*t_2*l_2*p_2956800*l_1*p_53351664*t_1*l_1*p_1499520*l_2*p_53800616>")
check_lemma_2_2(x7b, a3, l, gs, hs, σ) # True

"""
It follows that $x_{7b}$, $a_3$, $\ell$, `gs`, and `hs` generate
$7^{1+4}$, and therefore that the entire subgroup $\nma{x_{7b}} \cong 7^{1+4}{:}\left( 3 \times 2.\sym{7} \right)$
lies in $\langle g_{7b}, h_{7b} \rangle$.
"""

"""
## $\left( 7^2{:} \left( 3 \times 2.\alt{4} \right) \times \psl{2}{7} \right){:}2$ <a id="norm7A2"></a>

Generators for this maximal subgroup are given by
"""

g7a2 = MM("<y_667h*x_160h*d_25fh*p_86127869*l_1*p_1499520*l_2*p_32065431*l_2*t_2*l_2*p_1943040*l_2*p_2396609*l_1*t_1*l_2*p_3840*l_1*p_467760*l_1*p_2095680*t_1*l_2*p_1457280*l_1*p_30852*t_1*l_2*p_2344320*l_2*p_85372357*l_1*p_10667520*t_1*l_2*p_2830080*l_2*p_42754019*l_2*p_1458240>")
h7a2 = MM("<y_108h*x_0bc1h*d_7c7h*p_82093353*l_2*p_2597760*l_1*p_32950576*l_1*t_2*l_1*p_1499520*l_1*p_21862536*l_1*t_2*l_2*p_2386560*l_2*p_10791*l_1*t_2*l_2*p_2597760*l_1*p_53355169*t_2*l_2*p_2830080*l_2*p_42674145*t_1*l_2*p_2956800*l_1*p_53373525*t_1*l_2*p_1457280*l_1*p_137669>")
L_N = (g7a2, h7a2)

"""
This is the normaliser of a 7A-pure subgroup of $\MM$ with structure $7^2$.
We claim this particular instance normalises the group generated by
"""

x7 = MM("M<y_2dh*x_1ecdh*d_0a6bh*p_137531918*l_1*p_2880*l_2*p_21408*l_2*p_662400>")
y7 = MM("M<y_3c6h*x_135fh*d_0f29h*p_20613236*l_1*p_2999040*l_1*p_11146740*t_2*l_2*p_2597760*l_1*p_32950570*l_2*t_2*l_2*p_1943040*l_2*p_21887651*l_2*t_2*l_2*p_2787840*l_2*p_9601*t_2*l_1*p_1499520*l_1*p_64043922*t_1*l_2*p_1985280*l_1*p_42677011*t_2*l_2*p_2597760*l_1*p_53840066*t_1*l_2*p_1985280*l_1*p_53459120>")
L_E = (x7, y7)

"""
Note that $x_7$ is as in [Theorem 2.18](#norm7A).  
Firstly, verify that $x_7$ and $y_7 \notin \langle x_7 \rangle$ are
commuting elements of order 7:
"""

# x7 was shown to have order 7 in the proof of Theorem 2.18
y7.order() # 7
x7**y7 == x7 # True
y7 in [x7**i for i in range(1, 7)] # False

"""
It follows that $\langle x_7, y_7 \rangle \cong 7^2$.
As for 7A-purity, recall from [Theorem 2.18](#norm7A) that $x_7 \in \textrm{7A}$.
Since all powers of 7A elements in $\MM$ other than the identity are themselves
7A elements, it thus suffices to conjugate $x_7$ to a generator of each of
the cyclic subgroups of order 7 in $\langle x_7, y_7 \rangle$.
A set of generators (excluding $x_7$, which is already known to lie in 7A)
and of conjugating elements is as follows. Note that all conjugating elements
belong to $\langle g_{7a2}, h_{7a2} \rangle$.
"""

cyclic_gens = [y7] + [x7*y7**i for i in range(1, 7)]
conjugators = [g7a2*h7a2**2*g7a2**2, g7a2*h7a2**2, g7a2**3, g7a2*h7a2**2*g7a2*h7a2*g7a2, g7a2, g7a2**2*h7a2*g7a2*h7a2**2, (g7a2*h7a2)**2]
all([x7**conjugators[i] == cyclic_gens[i] for i in range(len(cyclic_gens))]) # True

"""
With that settled, show the claimed generators belong to the normaliser of $\langle x_7, y_7 \rangle$.
"""

map_7_2 = map_to_vectors(L_E)
check_normalise(L_E, L_N, group_set=map_7_2) # True

"""
As for showing the entire normaliser of structure $\left( 7^2{:} \left( 3 \times 2.\alt{4} \right) \times \psl{2}{7} \right){:}2$ is generated,
begin by verifying that the homomorphism induced
by $\langle g_{7a2}, h_{7a2} \rangle$'s action on $\langle x_7, y_7 \rangle$
has an image of size $\left| 3 \times 2.\alt{4} \right| \left| 2 \right| =
    3 \cdot 2 \cdot 12 \cdot 2 = 144$:
"""

size_image(L_N, map_7_2, basis=L_E) # 144

"""
It thus suffices to prove that the centraliser $7^2 \times \psl{2}{7}$ is contained
in $\langle g_{7a2}, h_{7a2} \rangle$. The factor $7^2$ is necessarily
$\langle x_7, y_7 \rangle$, with the former generator shown above to be conjugate
to the latter by an element of $\langle g_{7a2}, h_{7a2} \rangle$, so that
for the $7^2$ it suffices to exhibit a word in $g_{7a2}$ and $h_{7a2}$ equal
to $y_7$:
"""

(g7a2**3*h7a2**4*g7a2)**18 == y7 # True

"""
We claim that the factor $\psl{2}{7}$ is generated by the following two elements.
of $C_\MM \left( \langle x_7, y_7 \rangle \right)$.
"""

s = (h7a2**4*g7a2**4)**7
s.order() # 3
s**x7 == s**y7 == s # True
t = (g7a2**3*h7a2*g7a2*h7a2**3*g7a2*h7a2)**14
t.order() # 2
t**x7 == t**y7 == t # True

"""
Since 3 and 2 are relatively prime to $7^2$, these elements certainly lie
in the factor $\psl{2}{7}$ of the centraliser. To confirm that they generate it,
and thus complete the proof, apply `test_xsl` to $st$ and $t$.
"""

test_xsl(s*t, t, 7) # True

"""
## $7^{2+1+2}{:}\ling{2}{7}$ <a id="norm7B2"></a>

Generators for this maximal subgroup are given by
"""

g7b2 = MM("M<y_6c7h*x_7dah*d_8f2h*p_35966088*l_2*p_466560*l_2*p_21797088*l_2*t_1*l_1*p_1457280*l_2*p_12107809*l_2*t_2*l_2*p_1457280*l_1*p_12998001*l_2*t_2*l_1*p_2640000*l_1*p_957304*t_2*l_1*p_2880*l_1*p_4032*l_1*p_2799360*t_2*l_2*p_464640*l_1*p_63994224*t_2*l_2*p_1900800*l_2*p_17312>")
h7b2 = MM("M<y_5dh*x_1e0h*d_410h*p_222415221*l_1*p_1457280*l_2*p_2369716*l_1*t_2*l_2*p_2830080*l_2*p_23193138*l_1*t_1*l_2*p_1900800*l_2*p_12114711*l_2*t_2*l_1*p_1457280*l_2*p_14426*t_2*l_2*p_2386560*l_2*p_106705552*t_2*l_2*p_2597760*l_1*p_42717425*t_2*l_1*p_2027520*l_1*p_496522*t_2*l_2*p_1457280*l_1*p_73177>")
L_N = (g7b2, h7b2)

"""
This is the normaliser of a 7B-pure $7^2$ in the Monster which is embedded
in the normal subgroup $7^{1+4}$ of the normaliser of an arbitrary one of its elements.
We claim this particular instance normalises $A = \langle x_{7b}, a_3 \rangle$,
where $x_{7b}, a_3$ are as in the proof of [Theorem 2.19](#norm7B):
"""

x7b = MM("M<y_5d3h*x_0a6dh*d_8d4h*p_111142481*l_1*p_2999040*l_1*p_43234193>")
a3 = MM("M<y_0a1h*x_29fh*d_115h*p_52081919*l_1*p_1457280*l_2*p_32504931*l_2*t_2*l_2*p_1900800*l_2*p_474338*l_2*t_1*l_1*p_2640000*l_1*p_21801761*l_1*t_1*l_2*p_2386560*l_2*p_64088184*t_1*l_1*p_2880*l_2*p_10666896*l_2*p_4290240*t_2*l_1*p_1499520*l_1*p_106664201*t_2*l_2*p_1943040*l_2*p_86279607>")
L_E = (x7b, a3)

"""
It was shown there that $x_{7b}$ is a 7B element commuting with the element $a_3 \in 7^{1+4}
    \backslash \langle x_{7b} \rangle$ of order 7. By Wilson's odd local paper,
the normaliser of $\langle x_{7b}, a_3 \rangle \cong 7^2$ therefore lies
in a maximal subgroup $7^{1+4}{:}\left( 3 \times 2.\sym{7} \right)$ or $7^{2+1+2}{:}\ling{2}{7}$ or $\MM$. The latter contains
elements of order 48, but not the former (since 16 is not an element order
in $2.\sym{7}$), so that the first possibility may be eliminated by exhibiting
an element of order 48 in the relevant normaliser:
"""

map_7_2 = map_to_vectors(L_E)
check_normalise(L_E, L_N, group_set=map_7_2) # True
(g7b2*h7b2**2).order() # 48

"""
We have incidentally proved that the claimed generators belong to the normaliser
of $\langle x_{7b}, a_3 \rangle$.

As for showing the entire $7^{2+1+2}{:}\ling{2}{7}$ is generated, begin by verifying that
the homomorphism induced by $\langle g_{7b2}, h_{7b2} \rangle$'s action
on $\langle x_{7b}, a_3 \rangle$ has an image of size 672.
"""

size_image(L_N, map_7_2, basis=L_E) # 672

"""
Now, recall from the proof of [Theorem 2.19](#norm7B) that
$x_{7b}$, $a_3$, and certain elements $\ell, \left\{ g_i \right\}_{i=1}^1,
    \left\{ h_i \right\}_{i=1}^1, \sigma$ satisfy the conditions of
Lemma 2.2 with $p = 7$ and $k = 1$. The elements
$x_{7b}, y_{7b}, g_1, h_1, h_1^{\sigma}$ therefore generate a 7-group
lying in $\cma{x_{7b}, a_3}$ of order at least $7^5$. These in fact lie in
$g_{7b2}, h_{7b2}$:
"""

# The aforementioned elements
gs = [MM("M<y_714h*x_0fbch*d_680h*p_104733485*l_1*p_3840*l_2*p_22746528*t_2*l_1*p_2640000*l_1*p_12106888*l_1*t_2*l_2*p_3840*l_2*p_10666752*l_2*p_150720*t_2*l_1*p_1457280*l_2*p_934274*t_2*l_2*p_1985280*l_1*p_64045846*t_1*l_1*p_2999040*l_1*p_495478*t_2*l_2*p_2830080*l_2*p_43260121>")]
hs = [MM("M<y_24h*x_15d3h*d_6bdh*p_221822572*l_2*p_2787840*l_2*p_32130697*l_1*t_1*l_2*p_2597760*l_1*p_10672403*l_2*t_1*l_2*p_1985280*l_1*p_32071298*l_2*t_2*l_2*p_1457280*l_1*p_1483638*t_1*l_2*p_1985280*l_1*p_86258530*t_1*l_2*p_2956800*l_1*p_42671270*t_1*l_2*p_2597760*l_1*p_21338020>")]
σ = MM("M<y_355h*x_0df5h*d_0af9h*p_129634698*l_1*p_1858560*l_2*p_4032*l_1*p_10292160*t_2*l_2*p_1858560*l_2*p_33434352*l_2*t_2*l_1*p_1457280*l_2*p_12175332*l_2*t_1*l_2*p_2344320*l_2*p_10566*t_1*l_1*p_2640000*l_1*p_50065*t_2*l_2*p_2597760*l_1*p_21893138*l_1*t_2*l_2*p_2956800*l_1*p_53351664*t_1*l_1*p_1499520*l_2*p_53800616>")

x = (h7b2**2*g7b2*h7b2**2)/(g7b2**2*h7b2*g7b2**2)
y = (h7b2*g7b2)**3/(g7b2*h7b2)**3
L = [x**(1/g7b2)*y/x**3, x**(1/h7b2)/y*x**2, x**(g7b2**-2)*x**2*y]

x7b == L[0]/L[1]/L[2]**2 # True
a3 == L[2]/L[0]/L[1]**2 # True
gs[0] == L[0]/L[1]**2/L[2] # True
hs[0] == (L[1]**3*y**2/x)**2 # True
hs[0]**σ == L[2]**2*x/y # True

"""
The final factor of $\left| \ling{2}{7} \right|/672 = 3$ in the order of
the centraliser may be addressed by exhibiting an element of order 3 commuting with
$x_{7b}, a_3$. Such an element certainly cannot lie in the 7-group above, and
hence extends the group found so far to one at least thrice as large.
"""

t = ((h7b2*g7b2**3*h7b2)/(g7b2*h7b2**3*g7b2))**7
x7b*t == t*x7b # True
a3*t == t*a3 # True
t.order() # 3

"""
Thus $\langle g_{7b2}, h_{7b2} \rangle \le \nma{x_{7b}, a_3} \le 7^{2+1+2}{:}\ling{2}{7}$
has the same order as $7^{2+1+2}{:}\ling{2}{7}$, establishing equality of the three groups.
"""

"""
## $7^2{:}\lins{2}{7}$ <a id="norm7B2p"></a>
The following proof is adapted from Pisani and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

Our generators for this maximal subgroup are
"""

x7b = MM("M<y_5d3h*x_0a6dh*d_8d4h*p_111142481*l_1*p_2999040*l_1*p_43234193>")
y7b = MM("M<y_4a9h*x_1744h*d_0c88h*p_124439088*l_2*p_2597760*l_1*p_10860102*t_1*l_2*p_2386560*l_2*p_10772578*t_1*l_2*p_2956800*l_1*p_53817946*t_1*l_2*p_1858560*l_2*p_21333360*t_2*l_2*p_2830080*l_2*p_85837074*l_2*p_11151360*t_1*l_1*p_1457280*l_2*p_12549552*l_2>")
x4 = MM("M<y_406h*x_1bfeh*d_4d7h*p_44119992*l_2*p_2597760*l_1*p_33391058*l_2*t_1*l_1*p_2640000*l_1*p_12994999*l_1*t_1*l_2*p_2344320*l_2*p_1465428*l_1*t_1*l_1*p_2999040*l_1*p_5762*t_1*l_2*p_1985280*l_1*p_85413713*t_1*l_2*p_1943040*l_2*p_21367881*t_2*l_1*p_2027520*l_1*p_54866*t_1*l_1*p_1457280*l_2*p_76963>")
x14 = MM("M<y_599h*x_237h*d_0e76h*p_139011497*l_2*p_2956800*l_1*p_1912825*l_1*t_1*l_2*p_2787840*l_2*p_33397891*l_1*t_1*l_2*p_1393920*l_1*p_22416*l_2*p_2475840*t_2*l_2*p_2956800*l_1*p_10702214*t_2*l_1*p_2640000*l_1*p_661025*l_2*t_1*l_1*p_1457280*l_2*p_96458467*l_2*p_464640>")

"""
Note $x_{7b}$ is as in [Theorem 2.19](#norm7B).
This is the normaliser of a 7B-pure $7^2$ in the Monster not embedded
in the normal subgroup $7^{1+4}$ of the normaliser of an arbitrary one of its elements.
We claim this particular instance normalises $A = \langle x_{7b}, y_{7b} \rangle$.
"""

L_E = (x7b, y7b)

"""
As such, first confirm that $x_{7b}$ and $y_{7b}$ commute, have order 7, and are not powers of each other.
"""

# x7b was shown to have order 7 in proving Theorem 2.19
y7b.order() # 7
x7b_cyc = [x7b**i for i in range(7)]
x7b*y7b == y7b*x7b and not(y7b in x7b_cyc) # True

"""
For 7B-purity, recall from the proof of [Theorem 2.19](#norm7B)
that $x_{7b}$ is a 7B element of the Monster. Since all powers of 7B elements in $\MM$ other than the identity
are themselves 7B elements, it suffices to conjugate $x_{7b}$ to a generator
of each of the other seven cyclic subgroups of order $7$ in $A \cong 7^2$.
A set of generators is as follows.
"""

cyclic_gens = [y7b, y7b*x7b, y7b**2*x7b, y7b**3*x7b, y7b**4*x7b, y7b**5*x7b, y7b**6*x7b]

"""
A corresponding set of conjugating elements is as follows.
"""

conjugators = [(x14*x4*x14)**2, 
               (x14*x4*x14)**2*x14**2*x4, 
               x14*x4*x14**4*x4*x14, 
               x14*x4*x14**3, 
               x4*x14*(x14*x4)**2, 
               x14*x4*x14**3*x4, 
               (x14*x4*x14)**2*x14**3]

all([x7b**conjugators[i] == cyclic_gens[i] for i in range(len(cyclic_gens))]) # True

"""
It remains to show that $A$ does not lie in the normal subgroup $7^{1+4}$
of $\nma{x_{7b}}$. This subgroup $Q$ is generated by the for elements
$a_0, a_1, a_2, a_3$ defined in the proof of [Theorem 2.19](#norm7B);
show that $y_{7b} \not \in Q$ by checking that $y_{7b}$ does not commute modulo $\langle x_{7b} \rangle$ with $g_0$.
"""

a0 = MM("M<y_3c4h*x_1c6bh*d_225h*p_238190910*l_2*p_22080*l_1*p_21456*t_2*l_2*p_2344320*l_2*p_22307972*l_2*t_1*l_1*p_2640000*l_1*p_2413941*l_1*t_1*l_2*p_2830080*l_2*p_85332882*t_2*l_1*p_1499520*l_1*p_85414673*t_1*l_2*p_2597760*l_1*p_85814004*l_1*p_21333120*t_1*l_2*p_2830080*l_2*p_22304977*l_1>")
comm(y7b, a0) in x7b_cyc # False

"""
With that settled, show the claimed generators belong to the normaliser of $\langle x_{7b}, y_{7b} \rangle$.
"""

# x7b and y7b clearly normalise the group they generate
check_normalise(L_E, (x4, x14)) # True

"""
As for showing the entire normaliser $7^2{:}\lins{2}{7}$ is generated, check that
$x_4$ and $x_{14}$ satisfy Campbell and Robertson's presentation for $\lins{2}{7}$.
"""

(x4*x14)**3*x4**-2 == (x4*x14**4*x4*x14**4)**2*x14**7*x4**4 == e # True

"""
Check that $\left| x_{14} \right|=14$, which confirms that $B = \langle x_4,x_{14} \rangle$
is isomorphic to $\lins{2}{7}$: no proper quotient of $\lins{2}{7}$ contains an element
of order 14.
"""

x14.order() # 14

"""
Finally, check that $x_2 = x_4^2$ has order 2 and commutes with $x_{14}$, so that
$x_2$ is the central involution in $B$, and show that it does not centralise $x_{7b}$.
"""

x2 = x4**2
x2.order() # 2
x2*x14 == x14*x2 # True
x7b**x2 == 1/x7b # True

"""
It follows that $B$ intersects $A \cong 7^2$ trivially: "if not, then
the kernel of the action of $B$ on $A$ by conjugation must be non-trivial
because $A$ is abelian, and so the central involution in $B$ [which is
in all normal subgroups of $\lins{2}{7}$, e.g. kernels of homomorphisms]
must centralise $A$." (Pisani and Popiel, p. 4)

Hence, $\langle x_{7b}, y_{7b}, x_4, x_{14} \rangle$ is a subgroup
of $A$'s normaliser $7^2{:}\lins{2}{7}$ with order at least
$7^2 \left| 7^2{:}\lins{2}{7} \right| = \left| 7^2{:}\lins{2}{7} \right|$,
which can only be the entire normaliser.
"""

"""
## $11^2{:}\left( 5 {\times} 2.\alt{5} \right)$ <a id="norm11_2"></a>
The following proof is adapted from Pisani and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

Our generators for this maximal subgroup are as follows.
"""

x11 = MM("M<y_4bdh*x_120h*d_52ch*p_87984372*l_1*p_3840*l_1*p_21360*l_1*p_135360>")
y11 = MM("M<y_389h*x_0d8dh*d_0d9ch*p_150523146*l_1*p_2640000*l_1*p_10668793*t_1*l_2*p_2597760*l_1*p_21348617*t_1*l_1*p_2832000*t_1*l_1*p_1499520*l_2*p_63997801*t_1*l_1*p_1499520*l_2*p_1527956>")
x3 = MM("M<y_479h*x_474h*d_0ad8h*p_170818001*l_1*p_2999040*l_1*p_32071331*l_1*t_1*l_2*p_1920*l_1*p_1394256*l_1*t_2*l_2*p_1900800*l_2*p_21819090*l_1*t_1*l_2*p_2386560*l_2*p_10777289*t_1*l_1*p_1499520*l_2*p_42755921*t_1*l_2*p_2386560*l_2*p_42799217*t_2*l_2*p_1985280*l_1*p_53381138>")
x4 = MM("M<y_3d7h*x_1c77h*d_206h*p_198338203*l_1*p_2027520*l_1*p_22753408*l_2*t_1*l_2*p_467520*l_2*p_22260720*l_2*t_1*l_1*p_1415040*l_1*p_10666848*l_1*p_10539840*t_1*l_1*p_1933440*l_1*t_2*l_2*p_46168320*l_2*t_1*l_1*p_2999040*l_1*p_16357*t_1*l_2*p_2597760*l_1*p_86256657*t_1*l_2*p_2386560*l_2*p_21424635>")
x5 = MM("M<y_47ah*x_1f1eh*d_482h*p_238402577*l_2*p_1900800*l_2*p_33456466*t_2*l_1*p_1415040*l_1*p_10793664*t_2*l_2*p_1943040*l_2*p_42669319*t_2*l_2*p_2956800*l_1*p_85409964*t_2*l_1*p_2027520*l_1*p_96458484*l_2*p_11130240*t_1*l_2*p_1920*l_1*p_1296*l_1*p_4652160>")
L_N = (x11, y11, x3, x4, x5)

"""
This is the normaliser of the groups generated by two commuting elements of order 11 in the Monster.
We claim this particular instance normalises $\langle x_{11}, y_{11} \rangle$.
"""

L_E = (x11, y11)

"""
As such, first check that $x_{11}$ and $y_{11}$ have order $11$ and commute.
"""

x11.order() # 11
y11.order() # 11
x11*y11 == y11*x11 # True

"""
Then check that $y_{11} \not \in \langle x_{11} \rangle$.
"""

y11 in [x11**i for i in range(11)] # False

"""
With that settled, show the claimed generators belong to the normaliser of $\langle x_{11}, y_{11} \rangle$.
"""

# x11, y11 clearly normalise the group they generate
check_normalise(L_E, (x3, x4, x5)) # True

"""
As for showing the entire normaliser $11^2{:}\left( 5 {\times} 2.\alt{5} \right)$ is generated, confirm that $x_3$, $x_4$,
and $x_5$ have the orders indicated by their subscripts.
"""

x3.order() # 3
x4.order() # 4
x5.order() # 5

"""
Then check that $x_5$ commutes with $\langle x_3,x_4 \rangle$.
"""

(x3*x5 == x5*x3) and (x4*x5 == x5*x4) # True

"""
Check that $x_2 = x_4^2$ commutes with $x_3$, so is central in $\langle x_3,x_4 \rangle$.
"""

x2 = x4**2
x3*x2 == x2*x3 # True

"""
Show that, modulo $\langle x_2 \rangle$, $x_4$ and $x_3$ generate a group isomorphic to $\alt{5}$.
This is verified by checking the presentation $\langle a,b \mid a^2 = b^3 = (ab)^5 = 1 \rangle$ for $\alt{5}$ modulo $\langle x_2 \rangle$.
"""

(x4**2 in [e, x2]) and (x3**3 in [e, x2]) and ((x4*x3)**5 in [e, x2]) # True

"""
It follows that $\langle x_3, x_4 \rangle \cong 2.\alt{5}$ is centralised by an element $x_5$
of order 5; since no non-trivial power of such an element can be central in $2.\alt{5}$,
we have $\langle x_3, x_4, x_5 \rangle \cong 5 \times 2.\alt{5}$. This subgroup of
the normaliser contains no elements of order 11 and thus intersects
$\langle x_{11}, y_{11} \rangle \cong 11^2$ trivially, yielding the entire normaliser $11^2{:}\left( 5 {\times} 2.\alt{5} \right)$.
"""

"""
## $\left( 13{:}6 \times \psl{3}{3} \right) \udot 2$ <a id="norm13A"></a>
The following proof is adapted from one provided for the index 2 subgroup
$13{:}6 \times \psl{3}{3}$ by Dietrich, Lee, and Popiel. This construction
merely extends that group with an element $y_{12}$, the square of which is
the $y_6$ of Dietrich et al.

****

Generators are given by
"""

g13 = MM("M<y_519h*x_0cb8h*d_3abh*p_178084032*l_2*p_2344320*l_2*p_471482*l_1*t_1*l_2*p_2830080*l_2*p_22371347*l_2*t_2*l_1*p_1499520*l_2*p_22779365*l_2*t_1*l_2*p_2597760*l_1*p_11179396*t_1*l_1*p_1499520*l_2*p_85838017*t_2*l_1*p_1499520*l_1*p_64024721*t_2*l_2*p_2386560*l_2*p_21335269>")
y12 = MM("M<y_5c4h*x_0d78h*d_0ce0h*p_190945267*l_2*p_2344320*l_2*p_32475110*l_1*t_2*l_2*p_2597760*l_1*p_12134921*l_1*t_2*l_1*p_2880*l_2*p_3216*l_2*p_5180160*t_2*l_2*p_2787840*l_2*p_216480*t_2*l_2*p_2830080*l_2*p_42756901*t_1*l_2*p_1985280*l_1*p_11152936*t_1*l_2*p_2956800*l_1*p_85840900>")
c = MM("M<y_0fh*x_0bc4h*d_59h*p_207376512*l_2*p_1943040*l_2*p_22272232*l_2*t_1*l_1*p_1499520*l_1*p_22439*l_1*t_1*l_1*p_1394880*l_1*p_21456*l_2*p_4776960*t_2*l_1*p_1499520*l_2*p_53357227*t_1*l_2*p_960*l_2*p_10665792*l_1*p_6086400*t_1*l_2*p_1943040*l_2*p_64043939*t_2*l_2*p_2956800*l_1*p_64017049>")
d = MM("M<y_5a8h*x_0bcdh*d_941h*p_205645390*l_2*p_2830080*l_2*p_8690*l_2*t_1*l_2*p_1900800*l_2*p_10675420*t_1*l_2*p_2597760*l_1*p_42728016*t_2*l_2*p_2597760*l_1*p_10729207*t_1*l_2*p_1985280*l_1*p_21338086*t_2*l_2*p_2597760*l_1*p_21359269*t_1*l_1*p_1499520*l_1*p_42755907>")
L_N = (g13, y12, c, d)

"""
This class of maximal subgroups are the normalisers of elements belonging to conjugacy class 13A.
Begin by showing that the above generators lie in the normaliser of $g_{13}$, an element of order 13.
"""

L_E = [g13]

# g13 clearly normalises the group it generates
g13.order() # 13
check_normalise(L_E, (y12, c, d)) # True

"""
Since $\GG$ contains no 13A elements, directly verifying the conjugacy class
of $g_{13}$ is hard. Instead, rule out the alternative by constructing a subgroup
of $g_{13}$'s normaliser with order not dividing that of a 13B normaliser:
"""

# Conjugate everything into G_x0 for speed using an element
# that takes y12^6, a 2B involution commuting with <c, d>, to z
# (verification omitted, as it is mathematically irrelevant)

conjugator = MM("M<y_4e2h*x_1c8eh*d_0a4eh*p_199351965*l_2*p_1985280*l_1*p_29906*l_2*t_1*l_1*p_2027520*l_1*p_13038213*l_1*t_2*l_1*p_1415040*l_1*p_22272*l_2*p_1914240*t_1*l_2*p_1985280*l_1*p_21357329*t_2*l_1*p_1457280*l_2*p_85818775*l_2*p_971520*t_1*l_2*p_1858560*l_1*p_2208*l_2*p_1904640>")
c_conj, d_conj = (c**conjugator).reduce(), (d**conjugator).reduce()
c_conj.in_G_x0() and d_conj.in_G_x0() # True

size_image((c_conj, d_conj), as_int) # 5616

"""
The 13B normaliser (considered in [Theorem 2.25](#norm13B)) has order
$13^3 \cdot 3 \cdot 4 \cdot 24$, which is indeed not divisible by 5616.

Now, observe that $\langle y_{12} \rangle$ acts faithfully on $g_{13}$,
since 6 is a primitive root modulo 13:
"""

y12.order() # 12
g13**y12 == g13**6 # True

"""
It therefore only remains to show the given generators generate the centraliser
$13 \times \psl{3}{3}$ of $g_{13}$. It follows from earlier
calculations that $\langle g_{13} \rangle$ and $\langle c, d \rangle$
have orders 13 and $5616 = \left| \psl{3}{3} \right|$, so that
it suffices to show these are subgroups of the centraliser with trivial intersection.
"""

g13*c == c*g13 # True
g13*d == d*g13 # True
(y12**2)*c == c*(y12**2) # True
(y12**2)*d == d*(y12**2) # True

"""
This establishes that $\langle c, d \rangle$ centralises both $g_{13}$
and $y_{12}^2$. It is thus a subgroup of the centraliser; on the other hand,
as $\langle y_{12} \rangle$ acts faithfully on $g_{13}$, the group
$\langle c, d \rangle$ cannot intersect $\langle g_{13} \rangle$.
"""

"""
## $13^{1+2}{:}\left( 3 \times 4.\sym{4} \right)$ <a id="norm13B"></a>
Generators are given by
"""

g13 = MM("M<y_519h*x_0cb8h*d_3abh*p_178084032*l_2*p_2344320*l_2*p_471482*l_1*t_1*l_2*p_2830080*l_2*p_22371347*l_2*t_2*l_1*p_1499520*l_2*p_22779365*l_2*t_1*l_2*p_2597760*l_1*p_11179396*t_1*l_1*p_1499520*l_2*p_85838017*t_2*l_1*p_1499520*l_1*p_64024721*t_2*l_2*p_2386560*l_2*p_21335269>")
c = MM("M<y_0fh*x_0bc4h*d_59h*p_207376512*l_2*p_1943040*l_2*p_22272232*l_2*t_1*l_1*p_1499520*l_1*p_22439*l_1*t_1*l_1*p_1394880*l_1*p_21456*l_2*p_4776960*t_2*l_1*p_1499520*l_2*p_53357227*t_1*l_2*p_960*l_2*p_10665792*l_1*p_6086400*t_1*l_2*p_1943040*l_2*p_64043939*t_2*l_2*p_2956800*l_1*p_64017049>")
c2 = MM("M<y_79ch*x_0c7dh*d_944h*p_77869291*l_1*p_2027520*l_1*p_11601784*l_1*t_2*l_2*p_2830080*l_2*p_31997172*l_2*t_2*l_2*p_1985280*l_1*p_2418728*l_1*t_2*l_1*p_1499520*l_2*p_127991658*t_1*l_2*p_1900800*l_2*p_528273*t_2*l_2*p_1900800*l_2*p_1868369*l_2*t_2*l_2*p_1920*l_2*p_85812144*t_2*l_1*p_1499520*l_1*p_86279586>")
x1 = MM("M<y_50ah*x_1241h*d_0efah*p_199140999*l_2*p_1900800*l_2*p_85092*t_1*l_2*p_1985280*l_1*p_33414099*l_2*t_2*l_2*p_2787840*l_2*p_1465424*l_2*t_2*l_2*p_1900800*l_2*p_4802*t_2*l_2*p_2956800*l_1*p_43594886*t_2*l_1*p_1499520*l_2*p_85330007*t_1*l_2*p_2386560*l_2*p_53884407*t_1*l_1*p_1499520*l_2*p_53815333>")
x2 = MM("M<y_5b1h*x_13fah*d_37h*p_232192719*l_2*p_1457280*l_1*p_11672163*t_1*l_2*p_2787840*l_2*p_471431*l_2*t_2*l_2*p_1985280*l_1*p_23263157*l_2*t_1*l_2*p_2597760*l_1*p_64020819*t_1*l_1*p_1499520*l_2*p_21424630*t_2*l_2*p_2956800*l_1*p_43176417*t_1*l_2*p_1900800*l_2*p_5776>")
L_N = (g13, c, c2, x1, x2)

"""
Note that $g_{13}$ and $c$ are as in [Theorem 2.24](#norm13A).  
This subgroup is the normaliser of a 13B element in the Monster. We claim this particular instance normalises $c$.
"""

L_E = [c]

"""
Firstly, verify $c$ belongs to the correct conjugacy class:
"""

# This is the same element conjugator as in the proof of Theorem 2.24
conjugator = MM("M<y_4e2h*x_1c8eh*d_0a4eh*p_199351965*l_2*p_1985280*l_1*p_29906*l_2*t_1*l_1*p_2027520*l_1*p_13038213*l_1*t_2*l_1*p_1415040*l_1*p_22272*l_2*p_1914240*t_1*l_2*p_1985280*l_1*p_21357329*t_2*l_1*p_1457280*l_2*p_85818775*l_2*p_971520*t_1*l_2*p_1858560*l_1*p_2208*l_2*p_1904640>")

c_conj = (c**conjugator).reduce()
c_conj.order() # 13
c_conj.in_G_x0() # True

# Check the value of chi_M is a mere failsafe;
# all elements of order 13 in G_x0 belong to Monster class 13B!

c_conj.chi_G_x0()[0] # -2

"""
With that settled, show the claimed generators belong to the normaliser of $x_7$.
"""

# c clearly normalises the group it generates
check_normalise(L_E, (g13, c2, x1, x2)) # True

"""
As for generating the whole normaliser, we first demonstrate that
$c_2, g_{13}$ are elements of order 13 in the centraliser of $c$
which commute modulo $c$, ensuring that $\langle c, c_2, g_{13} \rangle$
is a 13-group.
"""

c*c2 == c2*c # True
c*g13 == g13*c # True
comm(c2, g13) in [c**i for i in range(13)] # True

"""
To verify that $\langle c, c_2, g_{13} \rangle$
has order (at least) $\left| 13^{1+2} \right| = 13^3$,
it then suffices to exhibit trivially intersecting
subgroups of orders $13^2$ and $13 = \left| g_{13} \right|$:
"""

map_13_2 = map_to_vectors((c, c2), 13)
len(map_13_2) # 169
as_int(g13) in map_13_2 # False

"""
The remainder of the normaliser then emerges upon
determining that $x_1, x_2$ generates a subgroup thereof
containing $\left| 3 \times 4.\alt{4} \right| = 3 \cdot 4 \cdot 24 =
    288$ elements: since $13 \not\mid 288$ and all elements of
$13^{1+2}$ except the identity must have order divisible by 13,
the intersection of this group and $\langle g_{13}, c, c_2 \rangle$
is trivial.
"""

# Conjugate everything into G_x0 for speed using x2,
# the third power of which is a 2B involution commuting with <x1, x2>
# (verification omitted, as it is mathematically irrelevant)

conjugator = (x2**3).conjugate_involution()[1]
x1_conj, x2_conj = (x1**conjugator).reduce(), (x2**conjugator).reduce()
size_image((x1_conj, x2_conj), as_int) # 288

"""
## $13^2{:}\lins{2}{13}{:}4$ <a id="norm13B2"></a>
Generators are given by
"""

c = MM("M<y_0fh*x_0bc4h*d_59h*p_207376512*l_2*p_1943040*l_2*p_22272232*l_2*t_1*l_1*p_1499520*l_1*p_22439*l_1*t_1*l_1*p_1394880*l_1*p_21456*l_2*p_4776960*t_2*l_1*p_1499520*l_2*p_53357227*t_1*l_2*p_960*l_2*p_10665792*l_1*p_6086400*t_1*l_2*p_1943040*l_2*p_64043939*t_2*l_2*p_2956800*l_1*p_64017049>")
c2 = MM("M<y_79ch*x_0c7dh*d_944h*p_77869291*l_1*p_2027520*l_1*p_11601784*l_1*t_2*l_2*p_2830080*l_2*p_31997172*l_2*t_2*l_2*p_1985280*l_1*p_2418728*l_1*t_2*l_1*p_1499520*l_2*p_127991658*t_1*l_2*p_1900800*l_2*p_528273*t_2*l_2*p_1900800*l_2*p_1868369*l_2*t_2*l_2*p_1920*l_2*p_85812144*t_2*l_1*p_1499520*l_1*p_86279586>")
x1 = MM("M<y_27h*x_0bddh*d_0c7fh*p_74975270*l_2*p_1457280*l_1*p_13001609*l_2*t_1*l_1*p_2640000*l_1*p_2347666*l_1*t_1*l_2*p_1858560*l_1*p_464928*l_2*p_962880*t_1*l_1*p_1499520*l_2*p_21363050*t_2*l_1*p_1499520*l_1*p_42793465*t_2*l_2*p_2787840*l_2*p_47158*t_2*l_1*p_1499520*l_1*p_43170822>")
x2 = MM("M<y_424h*x_7e9h*d_0d78h*p_130606814*l_2*p_2344320*l_2*p_32510960*t_1*l_1*p_2999040*l_1*p_1394132*l_1*t_1*l_2*p_2880*l_1*p_1296*l_1*p_2980800*t_2*l_2*p_2956800*l_1*p_42672192*t_2*l_2*p_2344320*l_2*p_32067169*l_1*t_1*l_1*p_1499520*l_1*p_96038948*t_1*l_2*p_2956800*l_1*p_64004482>")
x4 = MM("M<y_71ch*x_0b04h*d_0a72h*p_51746617*l_2*p_562560*l_2*t_1*l_2*p_1943040*l_2*p_12594720*t_1*l_2*p_2597760*l_1*p_85329985*t_2*l_2*p_2597760*l_1*p_12599543*t_2*l_1*p_960*l_2*p_42706032*t_1*l_2*p_1985280*l_1*p_43237046*t_1*l_2*p_1943040*l_2*p_43705510>")
L_N = (c, c2, x1, x2, x4)

"""
Note that $c$ and $c_2$ are as in [Theorem 2.25](#norm13B).  
This subgroup is the normaliser of a 13B-pure $13^2$ in the Monster.
We claim this particular instance normalises $\langle c, c_2 \rangle$.
"""

L_E = (c, c2)

"""
Firstly, verify $c, c_2$ are commuting elements that generate a group of order $13^2 = 169$
in which all non-trivial elements are 13B; since it was shown in the proof of [Theorem 2.25](#norm13B)
that $c$ is in 13B and $c, c_2$ are commuting elements which generate a group of the desired
order, it only remains to check that all non-trivial elements of $\langle c, c_2 \rangle$
are conjugate to $c$. Furthermore, noting that all powers of 13B elements in $\MM$
other than the identity are themselves 13B elements, it suffices to conjugate $c$
to a generator of each of the other thirteen cyclic subgroups of order 13 in $\langle c, c_2 \rangle$.
A set of generators and of conjugating elements is as follows.
"""

cyclic_gens = [c2] + [c*c2**i for i in range(1, 13)]
p2 = (x2**3).reduce()
conjugators = [p2] + [p2*x1**(12*i + 13)*p2 for i in range(1, 13)]
all([c**conjugators[i] == cyclic_gens[i] for i in range(len(cyclic_gens))]) # True

"""
With that settled, show the claimed generators belong to the normaliser of $\langle c, c2 \rangle$.
"""

# c and c2 clearly normalise the group they generate
map_13_2 = map_to_vectors(L_E, 13)
check_normalise(L_E, (x1, x2, x4), group_set=map_13_2) # True

"""
As for generating the whole normaliser, the elements of the abelian normal subgroup
$\langle c, c_2 \rangle$ clearly act trivially on that subgroup. It thus suffices
to show $\langle x_1, x_2, x_4 \rangle$ generates $\left| \lins{2}{13}{:}4 \right|
    = 4 \left( 13^2 - 1 \right) \cdot 13 = 8736$ actions on this subgroup:
"""

size_image((x1, x2, x4), map_13_2, basis=L_E) # 8736

"""
## $41{:}40$ <a id="norm41"></a>
Generators are given by
"""

g41 = MM("M<y_466h*x_84bh*d_28ch*p_201168515*l_2*p_1943040*l_2*p_21873173*l_2*t_2*l_2*p_1457280*l_1*p_11665457*l_2*t_2*l_2*p_2787840*l_2*p_33415298*l_2*t_2*l_2*p_2830080*l_2*p_12105277*t_1*l_2*p_2597760*l_1*p_43161937*t_1*l_1*p_2027520*l_1*p_974592*t_1*l_2*p_2830080*l_2*p_42710796>")
h41 = MM("M<y_76h*x_1bfbh*d_3dh*p_76771257*l_1*p_1499520*l_2*p_21929801*l_1*t_1*l_2*p_2344320*l_2*p_11666240*l_1*t_1*l_2*p_2597760*l_1*p_12545584*l_1*t_1*l_2*p_1900800*l_2*p_90439*t_1*l_2*p_1943040*l_2*p_42714548*t_2*l_2*p_48829440*l_2*p_86972352*t_2*l_2*p_2597760*l_1*p_43161957>")
L_N = (g41, h41)

"""
This maximal subgroup is the normaliser for the single class of elements of order 41 in $\MM$.
The verification is thus fairly straightforward:
"""

L_E = [g41]

g41.order() # 41
g41**h41 == g41**22 # True

"""
Noting that 22 is a primitive root modulo 41, we thus have all 40 conjugates of $g_{41}$ and the complete normaliser.
"""

"""
# 2-local subgroups

## $2 \udot \BB$ <a id="norm2A"></a>
The following proof is adapted from Dietrich, Lee, and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

*Standard* generators are
"""

a = MM("M<y_0bdh*x_133h*d_0b03h*p_122433352*l_1*p_71005440*l_2*p_220471680*l_2*t_2*l_2*p_60360960*l_1*p_232890288*l_2*t_1*l_2*p_59473920*l_2*p_241760688*l_1*t_1*l_1*p_13326720*l_2>")
b = MM("M<y_480h*x_15a9h*d_800h*p_55059691*l_1*p_71005440*l_1*p_199182768*t_1*l_1*p_59917440*l_1*p_242647728*l_1*t_1*l_1*p_49716480*l_1*p_240430080*l_1*t_1*l_2*p_15987840*l_2*t_1*l_2*p_141081600>")
L_N = (a, b)

"""
The maximal subgroup $2 \udot \BB$ of $\MM$ is the centraliser of an involution of class 2A.
Our copy of this subgroup is the centraliser of the 'standard' 2A involution $y$ in mmgroup:
"""

y = MM("M<d_200h>")
L_E = [y]

"""
Confirm that $y$ is the standard 2A involution.
"""

y.conjugate_involution() # (1, M<1>)

"""
Show the elements $a$ and $b$ of $\MM$ centralise $y$.
"""

comm(y, a) == comm(y, b) == e # True

"""
We claim that $a$ and $b$ are "standard generators" for $C_\MM \left( y \right) \cong 2 \udot \BB$.
This means that $a$ and $b$ generate $C_\MM \left( y \right)$ and satisfy the following properties:

1. $a$ projects to the $\BB$-class 2C,
2. $b$ projects to the $\BB$-class 3A,
3. $ab$ projects to the $\BB$-class 55A.
4. $(ab)^3(ab^2)(ab)(ab^2)^2$ projects to an element of order $23$.

We first show that $a$ and $b$ generate $C_\MM \left( y \right)$. It suffices to exhibit
an element of order $17$ and an element of order $31$ in $\langle a, b \rangle$,
because no maximal subgroup of the quotient $\BB$ of $2 \udot \BB$ contains elements of both orders.
(For clarity, note they cannot generate $\BB \not\le 2 \udot \BB$.)
"""

((a*b*a*b*a*b*a*b**2*a*b*a*b**2*a*b*a*b)**2).order(), (a*b*a*b*a*b*a*b**2*a*b*a*b**2).order() # (17, 31)

"""
It now remains to show that $a$ and $b$ satisfy conditions 1-4. 

Consider the following elements of $\MM$, which have order $104$ and $78$, respectively, and centralise $y$.
"""

g104 = MM("M<y_9dh*x_10cbh*d_0ab9h*p_185877467*l_2*p_50603520*l_1*p_210270720*l_1*t_2*l_2*p_70561920*l_2*p_181885440*l_2*t_1*l_2*p_69231360*l_2*p_168579888*l_1*t_2*l_1*p_4012800*l_1*t_1*l_2*p_119792640>")
g78 = MM("M<y_163h*x_1489h*d_0a93h*p_107838533*l_2*p_70118400*l_2*p_12439680*t_1*l_1*p_45281280*l_2*p_71871360*l_1*t_2*l_1*p_71005440*l_2*p_179667888*l_1*t_2*l_2*p_60804480*l_1*p_152169888>")
g104.order() == 104 and g78.order() == 78 and comm(y, g104) == comm(y, g78) == e # True

"""
Now observe that $g_{104}^{26}=a$ and $g_{78}^{13}=b$. In particular, $\left| a \right|=4$ and $\left| b \right|=6$.
"""

g104**26 == a and g78**13 == b and a.order() == 4 and b.order() == 6 # True

"""
The GAP character table library indicates that 
- all elements of order $104$ in $2 \udot \BB$ power to $2 \udot \BB$-class 4A, and that the latter elements project to $\BB$-class 2C; 
- all elements of order $78$ in $2 \udot \BB$ power to $2 \udot \BB$-class 6A, and that the latter elements project to $\BB$-class 3A.

Therefore, $a$ and $b$ lie in the $2 \udot \BB$-classes 4A and 6A and project to the $\BB$-classes 2C and 3A, respectively. 

In particular, conditions 1 and 2 hold.

All elements of order $55$ in $2 \udot \BB$ project to the $\BB$-class 55A, so to check condition 3 it suffices to confirm that $ab$ has order $55$.
"""

(a*b).order() == 55 # True

"""
Finally, to check condition 4, it suffices to confirm that the 23rd power of $(ab)^3(ab^2)(ab)(ab^2)^2$ lies in $\langle y \rangle = \left\{ y, y^2 \right\}$.
"""

((a*b)**3*(a*b**2)*(a*b)*(a*b**2)**2)**23 in [y, y**2] # True

"""
## $\QStr \udot \CO$ <a id="norm2B"></a>
The following proof is adapted from Dietrich, Lee, and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

*Standard* generators for $\GG = C_\MM \left( z \right)$, an instance of the maximal subgroup
$\QStr \udot \CO$ of $\MM$, are given by
"""

a = MM("M<y_2feh*x_51h*d_6f2h*p_199553794*l_2*p_1900800*l_2*p_684120>")
b = MM("M<y_32bh*x_0e4h*d_30fh*p_81928987*l_2*p_2880*l_1*p_21312*l_1*p_10455360>")
L_N = (a, b)

L_E = [z]

"""
Verify $z$ is a 2B involution for certainty:
"""

z.conjugate_involution() # (2, M<1>)

"""
Now show that $a, b$ satisfy the conditions described in Section 2.5 of Dietrich et al. for standard generators of $\GG$.
"""

comm(a**2, b**3) == z # True
a*z == z*a # True
b*z == z*b # True

# check membership in G_x0
a.in_G_x0() and b.in_G_x0() # True

# check orders
a.order() # 4
b.order() # 6

# check G_x0-classes
a.chi_G_x0()[1] # -13
b.chi_G_x0()[1] # 2
b.chi_G_x0()[0] # -3

# check product in right class
(a*b).order() # 40
(1/(a*b)).chi_G_x0()[1] # 0
(1/(a*b)).chi_G_x0()[2] # 0

# check that element powers are not central in the subgroup generated by a and b
(a**2)*b == b*(a**2) # False
(b**2)*a == a*(b**2) # False
(b**3)*a == a*(b**3) # False

# check that a*b*a*(b^2) has order 6 in the quotient
# choices are 6 or 21, so if the latter, returns False
(a*b*a*b**2).order() % 6 # 0

# check that we can generate Q: construct j0,..,j23
dim_q([(a**2)**((a*b)**i) for i in range(24)]) # (25, True)

"""
## $2^2 \udot {}^2 \lie{E}{6}{2} {:} \sym{3}$ <a id="norm2A2"></a>
Generators are given by
"""

g2 = MM("M<y_3a5h*x_153ch*d_47h*p_154067048*l_2*p_1943040*l_2*p_33454549*l_1*t_2*l_2*p_60360960*l_2*p_212044848*l_2*t_1*l_1*p_59917440*l_2*p_169466928*l_1*t_2*l_1*p_4456320*l_2>")
h2 = MM("M<y_0b5h*x_0b3ah*d_735h*p_192529580*l_2*p_1920*l_2*p_23232*l_2*p_535680*t_2*l_2*p_70561920*l_1*p_193416960*l_2*t_2*l_1*p_60804480*l_2*p_169910448*l_1*t_2*l_1*p_4456320*l_2>")
L_N = (g2, h2)

"""
This is the normaliser of a 2A-pure $2^2$ in the Monster. We claim this particular instance normalises
the group $\tilde{E}$ generated by
"""

y = MM("M<d_200h>")
y1 = y**g2
L_E = [y, y1]

"""
Note that $y$ is as in [the argument for the 2A normaliser](#norm2A).  
Firstly, verify $L_E$ generates a 2A-pure $2^2$:
"""

y2 = y*y1
y2 == y1*y # True
y2 == y1**g2 # True

"""
Since $y_2 = yy_1$ and $y_1$ are conjugates of the 2A involution $y$
such that $y$, $y_1$ commute, it follows that $\tilde{E} = \langle y, y_1 \rangle$
is 2A-pure Klein four-group.

With that settled, show the claimed generators belong to the normaliser of $\tilde{E}$.
"""

check_normalise(L_E, L_N) # True

"""
As for showing the entire normaliser is generated, first show the action of
$\langle g_2, h_2 \rangle$ on $\tilde{E}$ generates
$6 = \left| \sym{3} \right|$ permutations,

It suffices to test the images of generators of $\tilde{E}$ under the action,
as the conjugation action is an automorphism on $\tilde{E}$.
"""

act_on_yy1 = lambda x: (as_int(y**x), as_int(y1**x))
size_image(L_N, act_on_yy1) # 6

"""
This is all possible permutations of $\tilde{E}$ under conjugation,
so that it only remains to prove that
$C_\MM \left( \tilde{E} \right) < \langle g_2, h_2 \rangle$.

This is a group with structure $2^2.{}^2 \text{E}_6 \left( 2 \right)$.
A 2023 paper by Craven shows that ${}^2 \text{E}_6 \left( 2 \right)$
has no subgroups with order divisible by both 13 and 19, so start
by exhibiting elements
in $C_\MM \left( \tilde{E} \right) \cap \langle g_2, h_2 \rangle$ which project
to elements of these orders:
"""

a = h2**2*g2**9
b = a*g2**3

a*y == y*a # True
b*y == y*b # True
a*y1 == y1*a # True
b*y1 == y1*b # True
(a**2).order() # 13
(b**2).order() # 19
a**2 in (y, y1, y2) # False
b**2 in (y, y1, y2) # False

"""
Since 13 and 19 are coprime to $2^2$, $a^2$ and $b^2$ are the desired elements.
To finish, it must then be proven that the $\tilde{E}$ (the $2^2$ group) lies in
$\langle g_2, h_2 \rangle$. Noting that $e$ is in this group trivially
and that $y_1^{\langle h_2 \rangle} = \left\{ y, y_1, y_2 \right\}$,
it in fact suffices to demonstrate $y_1 \in \langle g_2, h_2 \rangle$.
"""

(h2*g2)**14 == y1 # True

"""
## $2^{2+11+22} \udot \left( \MT{24} \times \sym{3} \right)$ <a id="norm2B2"></a>
Generators are given by
"""

g2b = MM("M<y_7b9h*x_12b1h*d_0d7bh*p_18553667*t_1>")
h2b = MM("M<y_7c2h*x_183h*d_5ddh*p_123465560*t_1>")
L_N = (g2b, h2b)

"""
This is the normaliser of a singular $2^2$ in the Monster. We claim this particular instance normalises
the group $\tilde{E}$ generated by
"""

z1 = z**MM("M<t_1>")
L_E = (z, z1)

"""
Note that $z$ is the standard 2B involution in mmgroup as usual.  
Firstly, verify $L_N$ generates a singular $2^2$ using `check_singular`:
"""

E, E_as_int = check_singular(L_E)

"""
With that settled, show the claimed generators belong to the normaliser of $\tilde{E}$.
"""

check_normalise(L_E, L_N, group_set=E_as_int) # True

"""
As for showing the entire normaliser is generated,
consider four families of elements in $\nm{\tilde{E}}$:
* the generators $\left( g_{2b}, h_{2b} \right)$, which (in particular) generate the $\sym{3}$;
"""

F1 = L_N

"""
* generators of the $\MT{24}$;
"""

c1 = g2b**2
c2 = h2b**3
F2 = (c1, c2)

"""
* 11 generators of the projection of $\cm{\tilde{E}} < \GG$ into $\CO$;
"""

F3 = ((c1*c2**7)**15, (c1*c2**14)**15, (c1*c2**19)**11, (c1**2*c2**7)**15, (c1**2*c2**9)**14, (c1**2*c2**11)**12, (c1**2*c2**14)**15, (c1**2*c2**16)**11, (c1**2*c2**17)**14, (c1**2*c2**18)**12, (c1**2*c2**21)**15)

"""
* and 24 generators of $\QQ \cap C_\MM \left( \tilde{E} \right)$.
"""

F4 = ((c1*c2)**12, (c1*c2**2)**10, (c1*c2**3)**10, (c1*c2**5)**12, (c1*c2**7)**30, (c1*c2**9)**11, (c1*c2**11)**15, (c1*c2**12)**12, (c1*c2**15)**12, (c1*c2**17)**14, (c1**2*c2)**15, (c1**2*c2**3)**10, (c1**2*c2**6)**8, (c1**2*c2**8)**10, (c1**2*c2**10)**12, (c1**2*c2**19)**8, (c1**2*c2**20)**12, (c1**3*c2)**12, (c1**3*c2**2)**11, (c1**3*c2**8)**15, (c1**3*c2**14)**14, (c1**3*c2**16)**15, (c1**3*c2**21)**10, (c1**4*c2**21)**15)

"""
First, show the action of $\langle g_{2b}, h_{2b} \rangle$ on $\tilde{E}$
generates $6 = \left| \sym{3} \right|$ permutations, while members of
the other 3 families act trivially.

It suffices to test the images of generators of $\tilde{E}$ under the action,
as the conjugation action is an automorphism on $\tilde{E}$.
"""

act_on_zz1 = lambda x: (as_int(z**x), as_int(z1**x))
size_image(L_N, act_on_zz1) # 6
size_image((*F2, *F3, *F4), act_on_zz1) # 1

"""
Now show that the action of $\langle \mathcal{F}_2 \rangle$ on $\QQ_U/U$ generates $\MT{24}$,
while members of the other 2 following families act trivially.

Firstly, exhibit a basis for $\QQ_{\tilde{E}}$. (Note that the first 7 elements
arise in various proofs below.)
"""

qe_basis = (
    z, z1,
    MM("M<d_684h>"),
    MM("M<d_65bh>"),
    MM("M<d_19h>"),
    MM("M<d_5a1h>"),
    MM("M<d_675h>"),
    MM("M<d_4b3h>"),
    MM("M<d_179h>"),
    MM("M<d_7bfh>"),
    MM("M<d_0ah>"),
    MM("M<d_4d0h>"),
    MM("M<d_6ah>")
)

# Verification
conj = (e, MM("M<t_2>"))
all(g**x == z for g, x in zip(L_E, conj)) # True
all((g**x).in_Q_x0() for g in qe_basis for x in conj) # True
dim_q(qe_basis) # (13, True)

"""
Prove that the elements of $\mathcal{F}_3$ and $\mathcal{F}_4$ act trivially
on $\QQ_{\tilde{E}}/\tilde{E}$. Note that, in order to work
modulo $\tilde{E} \cong 2^2$, we set `index=2` in `map_to_vectors`;
$\QQ_{\tilde{E}}$ is elementary abelian by Lemma 4.2 of
Meierfrankenfeld and Shpectorov.
"""

act_on_qe_e = map_to_vectors(qe_basis, index=2)
size_image((*F3, *F4), act_on_qe_e, basis=qe_basis[2:]) # 1

"""
As far as showing the factor $\MT{24}$ is generated by $\langle \mathcal{F}_2 \rangle$,
it suffices to exhibit elements with actions of order 5, 23, and 21; none of
the three maximal subgroups of $\MT{24}$ with order divisible by both 5 and 23
has elements of order 21.
"""

# F3 = (c1, c2)
size_image([c1**3], act_on_qe_e, basis=qe_basis[2:]) # 5
size_image([c2], act_on_qe_e, basis=qe_basis[2:]) # 23
size_image([(c1*c2**6)**2], act_on_qe_e, basis=qe_basis[2:]) # 21

"""
Now, verifying that all elements of $\mathcal{F}_3$ and
$\mathcal{F}_4$ do indeed lie in $\GG = \QQ.\CO$ ...
"""

all(x.in_G_x0() for x in (*F3, *F4)) # True

"""
show that $\mathcal{F}_4$ generate $2^{11} = 2048$ cosets of $\QQ$ in $\GG$.
"""

size_image(F3, to_co1) # 2048

"""
Finally, verify that $\mathcal{F}_4$ generates a subgroup of $\QQ$
with order $2^{24}$. Note the second element of the output is True, so that
the result is trustworthy.
"""

dim_q(F4) # (24, True)

"""
In summary, it is possible to find in $\langle g_{2b}, h_{2b} \rangle \le \nm{\tilde{E}}$:
* $2^{24}$ elements of $\QQ$, all of which act trivially on $\QQ_{\tilde{E}}/\tilde{E}$
and $\tilde{E}$;
* $2^{11}$ elements of $\GG = \QQ.\CO$ which lie in distinct cosets of $\QQ$,
all of which act trivially on $\QQ_{\tilde{E}}/\tilde{E}$ and $\tilde{E}$;
* $\left| \MT{24} \right|$ elements of $\cm{\tilde{E}}$ which act differently
on $\QQ_{\tilde{E}}/\tilde{E}$, all of which act trivially on $\tilde{E}$; and
* $6 = \left| \sym{3} \right|$ elements which act differently on $\tilde{E}$.

It follows $\left| \langle g_{2b}, h_{2b} \rangle \right| \ge 2^{24} \cdot 2^{11} \left| \MT{24} \right|
\left| \sym{3} \right| = \left| 2^{2+11+22} \udot \left( \MT{24} \times \sym{3} \right) \right|$,
so that $\langle g_{2b}, h_{2b} \rangle = \nm{\tilde{E}}$.
"""

"""
## $2^{3+6+12+18} \udot \left( \psl{3}{2} \times 3.\sym{6} \right)$ <a id="norm2B3"></a>
Generators are given by
"""

g3 = MM("M<y_462h*x_611h*d_90fh*p_40550696*l_1*p_57699840*t_1>")
h3 = MM("M<y_2ebh*x_1317h*d_5cdh*p_216349744*t_1>")
L_N = (g3, h3)

"""
This is the normaliser of a singular $2^3$ in the Monster. We claim this particular instance normalises
the group $\tilde{E}$ generated by
"""

z1 = z**MM("M<t_1>")
w = MM("M<d_684h>")
L_E = (z, z1, w)

"""
Note that $z, z_1$ are as in [Theorem 3.6](#norm2B2).  
Firstly, verify $L_E$ generates a singular $2^3$ using `check_singular`:
"""

E, E_as_int = check_singular(L_E)

"""
With that settled, show the claimed generators belong to the normaliser of $\tilde{E}$.
"""

check_normalise(L_E, L_N, group_set=E_as_int) # True

"""
As for showing the entire normaliser is generated, consider four families of elements
in $\nm{\tilde{E}}$:
* the generators $\left( g_3, h_3 \right)$, which (in particular) generate the $\psl{3}{2}$;
"""

F1 = L_N

"""
* generators of the $3.\sym{6}$;
"""

c1 = (h3**2*g3)**2
c2 = (g3**3*h3*g3*h3*g3**2*h3*g3)/(h3**2*g3*h3*g3**3*h3**2)
F2 = (c1, c2)

"""
* 6+6=12 generators of the projection of $\cm{\tilde{E}} < \GG$ into $\CO$;
"""

F3 = (c2*c1*c2*c1**2/(c2*c1*c2), c2**3*c1**2/(c2**3), c2*c1*c2**2*c1**2/(c2*c1*c2**2), c1**2, c1*c2**2*c1**2/(c1*c2**2), (c2*c1*c2**6)/(c2*c1), c1*c2**6/c1, c1*c2**2*c1*c2**6/(c1*c2**2*c1), (c1*c2)**2*c1**2/(c1*c2)**2, (c2*c1)**2*c2**6/(c2*c1)**2, c2**6/c1**2, c2**2*c1*c2**6/(c2**2*c1))

"""
* and 22 generators of $\QQ \cap \cm{\tilde{E}}$.
"""

F4 = (h3**6*h3**9/h3**3/(h3**1*h3**2/h3**3), g3**8*h3**3*h3**9/g3**1/g3**7/(h3**1*h3**2/h3**3), h3**3*g3**4*h3**6/g3**4/h3**9/(h3**9*g3**4*h3**6/g3**4/h3**3), g3**3*h3**2*g3**9*h3**2/(g3**1*h3**1*g3**5)/(g3**5*h3**4*g3**5*h3**7/(h3**2*g3**2))/(g3**4*h3**7*g3**4*h3**9/(g3**4*h3**1*g3**4)/h3**3), h3**6*g3**4*h3**6/g3**4/(h3**3*h3**9)/(g3**4*h3**6/g3**4/h3**6), g3**7*h3**6*g3**6*h3**6/g3**6/(h3**6*g3**7*h3**6)/(g3**4*h3**6/g3**4/h3**6), g3**4*h3**1*g3**5*h3**9/(g3**4*h3**1*g3**5)/(g3**9*h3**7*g3**7*h3**5/g3**2)/(h3**3*g3**4*h3**3/g3**4/h3**6), g3**8*h3**9*g3**8*h3**9/g3**2/(g3**8*h3**6*g3**6)/(h3**9*g3**4*h3**9/g3**4/h3**6), g3**8*h3**6*g3**8*h3**3/g3**2/(g3**8*h3**9*g3**6)/(h3**6*g3**4*h3**3/g3**4/h3**9), g3**6*h3**9*g3**7*h3**9/g3**6/(g3**2*h3**9*g3**7*h3**9/g3**2)/(h3**9*g3**8*h3**3/g3**1/g3**7), g3**9*h3**6/g3**2/(g3**1*h3**6*g3**6)/(g3**1*h3**6*g3**8*h3**6/g3**2/g3**7), g3**2*g3**9*h3**6/g3**4/(g3**7*h3**6)/(g3**7*h3**6*g3**4*h3**6/g3**4/g3**7), g3**3*h3**7*g3**8*h3**8/(g3**2*h3**1*g3**5)/(g3**3*h3**1*g3**8*h3**2/(g3**2*h3**1*g3**5))/(g3**7*h3**2*g3**4*h3**6/(h3**2*g3**4)/(g3**7*h3**6)), h3**7*g3**4*h3**6/(h3**1*g3**4)/(h3**3*h3**9)/(g3**3*h3**6*g3**8*h3**3/g3**4/(g3**7*h3**9)), g3**8*h3**5*g3**6*h3**9/(h3**1*g3**5)/(g3**8*h3**5*g3**2*h3**9/(h3**1*g3**1))/(g3**1*h3**6*g3**4*h3**6/g3**5/(h3**3*h3**9)), g3**5*h3**3*g3**1*h3**3/g3**6/(g3**1*h3**3*g3**1*h3**3/g3**2)/(g3**8*h3**3*g3**3*h3**6/g3**4/(h3**3*g3**7*h3**6)), g3**8*h3**4*g3**3*h3**3/(g3**1*h3**1*g3**3)/(g3**3*h3**3*g3**5*h3**3/g3**1)/(g3**8*h3**6*g3**3*h3**9/g3**4/(h3**6*g3**7*h3**9)), g3**2*h3**3*g3**7*h3**6/g3**2/(g3**1*h3**6*g3**6*h3**3)/(g3**1*h3**4*g3**7*h3**8/g3**1/(h3**8*g3**7*h3**4)), g3**8*h3**8*g3**3*h3**6/(h3**1*g3**2)/(g3**2*h3**6*g3**5*h3**9)/(g3**3*h3**7*g3**7*h3**8/g3**3/(h3**8*g3**7*h3**7)), g3**4*h3**7*g3**3*h3**3/(g3**4*h3**1*g3**3)/(h3**7*g3**3*h3**3/(h3**1*g3**3))/(g3**5*h3**2*g3**5*h3**3/(g3**4*h3**1*g3**4)/(g3**1*h3**2*g3**1*h3**2)), g3**3*h3**8*g3**2/(g3**1*h3**1*g3**5*h3**1)/(g3**1*h3**7*g3**7/(g3**1*h3**1))/(g3**4*h3**8*g3**1*h3**2/g3**3/(g3**1*h3**2*g3**1*h3**8)), g3**7*h3**2*g3**5*h3**6/(h3**2*g3**5)/(g3**1*h3**6*g3**6)/(g3**3*h3**5*g3**8/(g3**2*h3**1)/(g3**1*h3**2*g3**8*h3**2)))

"""
First, show the action of $\langle g_3, h_3 \rangle$ on $\tilde{E}$
generates $168 = \left| \psl{3}{2} \right|$ permutations,
while members of the other 3 families act trivially.

It suffices to test the images of generators of $\tilde{E}$ under the action,
as the conjugation action is an automorphism on $\tilde{E}$.
"""

act_on_zz1w = map_to_vectors(L_E)
size_image(L_N, act_on_zz1w, basis=L_E) # 168
size_image((*F2, *F3, *F4), act_on_zz1w, basis=L_E) # 1

"""
Now show that the action of $\langle \mathcal{F}_2 \rangle$
on $\QQ_{\tilde{E}}/\tilde{E}$ generates $2160 = \left| 3.\sym{6} \right|$ permutations,
while members of the other 2 following families act trivially.

Firstly, show that the first 9 basis elements of $\QQ_{2^2}$ given
in the proof of [Theorem 3.6](#norm2B2) form a basis
for $\QQ_{\tilde{E}}$
"""

qe_basis = (
    z, z1, w,
    MM("M<d_65bh>"),
    MM("M<d_19h>"),
    MM("M<d_5a1h>"),
    MM("M<d_675h>"),
    MM("M<d_4b3h>"),
    MM("M<d_179h>"),
)

# Verification
conj = (e, g3**6, g3**5)
all(g**x == z for g, x in zip(L_E, conj)) # True
all((g**x).in_Q_x0() for g in qe_basis for x in conj) # True
dim_q(qe_basis) # (9, True)

"""
Prove the 2160 permutations are generated. Note that, in order to work modulo
$\tilde{E} \cong 2^3$, we set `index=3` in `map_to_vectors``; $\QQ_{\tilde{E}}$ is
elementary abelian by Lemma 4.2 of Meierfrankenfeld and Shpectorov.
"""

act_on_qe_e = map_to_vectors(qe_basis, index=3)
size_image(F2, act_on_qe_e, basis=qe_basis[3:]) # 2160
size_image((*F3, *F4), act_on_qe_e, basis=qe_basis[3:]) # 1

"""
Now, verifying that all elements of $\mathcal{F}_3$ and
$\mathcal{F}_4$ do indeed lie in $\GG = \QQ.\CO$ ...
"""

all(x.in_G_x0() for x in (*F3, *F4)) # True

"""
show that $\mathcal{F}_3$ generates (at least) $2^{16}$ cosets of $\QQ$ in $\GG$.
Because the full $2^{16}$ is a bit large, instead exhibit subsets of
$\mathcal{F}_3$ which generate $512 = 2^9$ and $512 = 2^9$ cosets,
respectively, with 4 in common ($2^9 \cdot 2^9/4 = 2^{16}$).
"""

set_1 = size_image(F3[:6], to_co1, set)
set_2 = size_image(F3[6:], to_co1, set)
len(set_1) # 512
len(set_2) # 512
len(set_1 & set_2) # 4

"""
Finally, verify that $\mathcal{F}_4$ generates a subgroup of $\QQ$ with order $2^{23}$.
Note the second element of the output is `True`, so that the result is trustworthy.
"""

dim_q(F4) # (23, True)

"""
In summary, it is possible to find in $\langle g_3, h_3 \rangle \le \nm{\tilde{E}}$:
* $2^{23}$ elements of $\QQ$, all of which act trivially
on $\QQ_{\tilde{E}}/\tilde{E}$ and $\tilde{E}$;
* $2^{16}$ elements of $\GG = \QQ.\CO$ which lie in distinct cosets of $\QQ$,
all of which act trivially on $\QQ_{\tilde{E}}/\tilde{E}$ and $\tilde{E}$;
* $2160 = \left| 3.\sym{6} \right|$ elements of $\cm{\tilde{E}}$ which act
differently on $QQ_{\tilde{E}}/\tilde{E}$, all of which act trivially on $\tilde{E}$; and
* $168 = \left| \psl{3}{2} \right|$ elements which act differently on $\tilde{E}$.

It follows $\left| \langle g_3, h_3 \rangle \right| \ge 2^{23} \cdot 2^{16} \left| 3.\sym{6} \right|
\left| \psl{3}{2} \right| = \left| 2^{3+6+12+18} \udot \left( \psl{3}{2} \times 3.\sym{6} \right) \right|$,
so that $\langle g_3, h_3 \rangle = \nm{\tilde{E}}$.
"""

"""
## $2^{5+10+20} \udot \left( \sym{3} \times \psl{5}{2} \right)$ <a id="norm2B5"></a>
Generators are given by
"""

g5 = MM("M<y_504h*x_4a2h*d_0edfh*p_29114354*l_1*p_57699840*t_1>")
h5 = MM("M<y_4fah*x_1fdfh*d_0a85h*p_32789328*l_1*p_57699840*t_1>")
L_N = (g5, h5)

"""
This is the normaliser of a singular $2^5$ of Type 2 in the Monster. We claim
this particular instance normalises the group $U$ generated by
"""

z = MM("M<x_1000h>")
z1 = z**MM("M<t_1>")
w = MM("M<d_684h>")
k4 = MM("M<d_65bh>")
k5 = MM("M<d_19h>")
L_E = (z, z1, w, k4, k5)

"""
Note that $z, z_1, w$ are as in [Theorem 3.7](#norm2B3).  
Firstly, verify $L_E$ generates a singular $2^5$ using `check_singular`:
"""

E, E_as_int = check_singular(L_E)

"""
In order to show $\tilde{E}$ is Type 2, it suffices to demonstrate
$\left| \QQ_{\tilde{E}} \right| = \left| \tilde{E} \right|$.
As a preliminary step, verify that
$V = \langle z, z_1, w, k_4 \rangle < \tilde{E}$ is a singular,
has order $2^4$, and that $\QQ_V$ contains the 128-element subgroup
$U$ generated by the first seven basis elements of $\QQ_{2^3}$ given
in the proof of [Theorem 3.7](#norm2B3):
"""

v_basis = (z, z1, w, k4)
V, V_as_int = check_singular(v_basis)

# The seven basis elements
qv_basis = (z, z1, w, k4, k5, MM("M<d_5a1h>"), MM("M<d_675h>"))
conj = [x.conjugate_involution()[1] for x in v_basis]
all((g**h).in_Q_x0() for g in qv_basis for h in conj) # True
qv = size_image(qv_basis, return_type=list, is_solv=True)
len(qv) # 128

"""
By Lemma 4.9 of Meierfrankenfeld and Shpectorov, $\QQ_V \cong 2^7$, so $\QQ_V = U$.
Since $\QQ_{\tilde{E}} = \QQ_V \cap \QQ_{k_5}$, it will follow
that $\left| \QQ_{\tilde{E}} \right| = \left| \tilde{E} \right|$.
if it can be proven $\QQ_V$ contains exactly
$\left| \tilde{E} \right| = 32$ elements of $\QQ_{k_5}$.
"""

unk5 = h5**14
k5**unk5 == z # True
len([x for x in qv if (x**unk5).in_Q_x0()]) # 32

"""
With that settled, show the claimed generators belong to the normaliser of $\tilde{E}$.
"""

check_normalise(L_E, L_N, group_set=E_as_int) # True

"""
As for showing the entire normaliser is generated,
consider four families of elements in $\nm{\tilde{E}}$:
* the generators $\left( g_5, h_5 \right)$, which (in particular) generate the $\psl{5}{2}$;
"""

F1 = L_N

"""
* generators of the $\sym{3}$;
"""

c1 = g5**15
c2 = h5**31
F2 = (c1, c2)

"""
* 8+6=14 generators of the projection of $\cm{\tilde{E}} < \GG$ into $\CO$;
"""

B0, B1 = c2*c1*c2/c1, c2**2*c1/(c1*c2)
F3 = (
    B0, B1, (c1**2)**h5, B0**g5, B0**h5, (c2*c1**2/c2)**h5, B1**g5,
    B1**h5, B0**(g5**2), B0**(g5*h5), B0**(h5*g5), B0**(h5**2),
    B1**(g5**2), B1**(h5**2)
)

"""
* and 20 generators of $\QQ \cap \cm{\tilde{E}}$.
"""

F4 = (F3[3]**2, F3[6]**2, F3[8]**2, F3[9]**2, F3[12]**2, F3[0]*F3[2]*F3[0], F3[2]*F3[10]**2, F3[2]*F3[13]**2, F3[5]*F3[7]**2, F3[5]*F3[11]**2, F3[1]**2*F3[4]**2, (F3[0]*F3[8])**g5/(F3[2]*F3[11]*F3[12]*F3[13]), F3[0]**g5*F3[8]**h5/F3[2], (F3[0]*F3[9])**g5/(F3[1]**2*F3[6]), F3[0]**g5*F3[9]**h5/(F3[3]*F3[4]*F3[5]*F3[7]), (F3[0]*F3[10])**g5/(F3[0]*F3[1]*F3[4]*F3[7]*F3[9]*F3[10]*F3[11]*F3[12]*F3[13]), F3[0]**g5*F3[10]**h5/(F3[0]*F3[1]*F3[3]*F3[4]*F3[7]*F3[11]*F3[12]*F3[9]*F3[10]*F3[13]), (F3[0]*F3[11])**g5/(F3[3]*F3[8]*F3[11]*F3[12]), F3[0]**g5*F3[11]**h5/(F3[0]*F3[4]*F3[7]*F3[8]*F3[3]*F3[10]), (F3[0]*F3[12])**g5/(F3[6]*F3[8]*F3[3]*F3[13]))

"""
First, show the action of $\langle g_5, h_5 \rangle$ on $\tilde{E}$ induces a group
isomorphic to $\psl{5}{2}$ while members of the other 3 families act trivially.

It suffices to test the images of generators of $\tilde{E}$ under the action,
as the conjugation action is an automorphism on $\tilde{E}$.
"""

act_on_e = map_to_vectors(L_E)
size_image((*F2, *F3, *F4), act_on_e, basis=L_E) # 1
size_image([g5], act_on_e, basis=L_E) # 15
size_image([h5], act_on_e, basis=L_E) # 31

"""
The actions of $g_5$ and $h_5$ on $\tilde{E}$, belonging
to $\aut{\tilde{E}} \cong \psl{5}{2}$, thus have order 15 and 31, respectively.
Data in the GAP character table library, however, reveals no maximal subgroup
of $\psl{5}{2}$ has order divisible by both 15 and 31;
they therefore lie in different maximal subgroups, generating that entire group.

Now show that the action of $\langle \mathcal{F}_3 \rangle$ on $\QQ_V/V$,
where $V = \langle z, z_1, w, k_4 \rangle$ is as defined above, generates
$6 = \left| \sym{3} \right|$ permutations, while members of the other 2
following families act trivially. First map elements of $\QQ_V$
to standard representatives of cosets of $V$.
"""

qv_v_map = {}
for x in qv:
    k = as_int(x)
    if k not in qv_v_map:
        for y in V:
            qv_v_map[as_int(x*y)] = k

"""
Perform the verifications; it suffices to test the images of generators of
$\QQ_V/V$ under the action, as the conjugation action is an automorphism
on $\QQ_V/V$.
"""

act_on_qv_v = lambda x: tuple(qv_v_map[as_int(q**x)] for q in qv_basis)
size_image(F2, act_on_qv_v) # 6
size_image((*F3, *F4), act_on_qv_v) # 1

"""
Now, verifying that all elements of $\mathcal{F}_3$ and
$\mathcal{F}_4$ do indeed lie in $\GG = \QQ.\CO$ ...
"""

all(x.in_G_x0() for x in (*F3, *F4)) # True

"""
show that $\mathcal{F}_3$ generates (at least) $2^{14}$ cosets of $\QQ$ in $\GG$.
Because the full $2^{14}$ is a bit large, instead exhibit subsets of
$\mathcal{F}_3$ which generate $256 = 2^8$ and $256 = 2^8$ cosets,
respectively, with 4 in common ($2^8 \cdot 2^8/4 = 2^{14}$).
"""

set_1 = size_image(F3[:8], to_co1, set)
set_2 = size_image(F3[8:], to_co1, set)
len(set_1) # 256
len(set_2) # 256
len(set_1 & set_2) # 4

"""
Finally, verify that $\mathcal{F}_4$ generates a subgroup of $\QQ$ with size $2^{21}$.
Note the second element of the output is `True`, so that the result is trustworthy.
"""

dim_q(F4) # (21, True)

"""
In summary, it is possible to find in $\langle g_5, h_5 \rangle \le \nm{\tilde{E}}$:
* $2^{21}$ elements of $\QQ$, all of which act trivially on $\QQ_V/V$ and $\tilde{E}$;
* $2^{14}$ elements of $\GG = \QQ.\CO$ which lie in distinct cosets of $\QQ$,
all of which act trivially on $\QQ_V/V$ and $\tilde{E}$;
* $6 = \left| \sym{3} \right|$ elements of $\cm{\tilde{E}}$ which act differently on $\QQ_V/V$,
all of which act trivially on $\tilde{E}$; and
* $\left| \psl{5}{2} \right|$ elements which act differently on $\tilde{E}$.

It follows $\left| \langle g_5, h_5 \rangle \right| \ge 2^{21} \cdot 2^{14} \left| \sym{3} \right|
\left| \psl{5}{2} \right| = \left| 2^{5+10+20} \udot \left( \sym{3} \times \psl{5}{2} \right) \right|$,
so that $\langle g_5, h_5 \rangle = \nm{\tilde{E}}$.
"""

"""
## $2^{10+16} \udot \orth+{10}{2}$ <a id="normArk"></a>
*Standard* generators are given by
"""

g10 = MM("M<y_1a6h*x_1cf8h*d_0d6fh*p_161209616*l_2*p_2349120*t_2*l_2*p_2936640*t_2*l_1*p_97173120>")
h10 = MM("M<y_26eh*x_1115h*d_0acdh*p_27244563*l_2*p_1523520*t_2*l_1*p_4651200*l_2*t_1*l_1*p_2449920>")
L_N = (g10, h10)

"""
This is the normaliser of an "ark" (i.e. a group containing a singular Type 1 $2^5$
and singular Type 2 $2^5$s embedding each index 2 subgroup therein) We claim
this particular instance normalises the ark $\tilde{E}$ generated by
"""

z = MM("M<x_1000h>")
z1 = z**MM("M<t_1>")
w = MM("M<d_684h>")
k4 = MM("M<d_65bh>")
k5 = MM("M<d_19h>")
ρ = MM("M<y_4efh*x_54fh*d_0dfh*p_77227505*t_1*l_1*p_824640*t_2*l_1*p_2809920>")
L_E = (z, z1, w, k4, k4**(ρ**16), k5, k5**(ρ**16), k5**ρ, k5**(ρ**30), k5**(ρ**15))

"""
which arises from the $2^5$ of Type 1 $T_1$ generated by
"""

T1_basis = L_E[:5]

"""
Note that $z, z_1, w, k_4, k_5$ are as in [Theorem 3.8](#norm2B5).  
Firstly, verify $T_1$ is a singular $2^5$ using check_singular:
"""

T1, T1_as_int = check_singular(T1_basis)

"""
In order to show it has Type 1, it suffices to demonstrate
$\left| \QQ_{T_1} \right| = 2 \left| T_1 \right|$. It was
verified in the proof of [Theorem 3.8](#norm2B5) that
that $V = \langle z, z_1, w, k_4 \rangle$ is singular,
with $\QQ_V$ generated by a given list of elements;
since $\QQ_{T_1} = \QQ_V \cap \QQ_{{\rho^{16}}}$, the required result
follows upon confirming $\QQ_V$ contains exactly
$2\left| T_1 \right| = 64$ elements of $\QQ_{k_4^{\rho^{16}}}$.
"""

# The aforementioned list of elements
qv_basis = (z, z1, w, k4, k5, MM("M<d_5a1h>"), MM("M<d_675h>"))
qv = size_image(qv_basis, return_type=list, is_solv=True)

unk_ = ρ**29
L_E[4]**unk_ == z # True
len([x for x in qv if (x**unk_).in_Q_x0()]) # 64

"""
In order to now show that $\tilde{E} > T_1$ is an ark, recall
from the proof of [Theorem 3.8](#norm2B5) that
$\langle z, z_1, w, k_4, k_5 \rangle < \tilde{E}$ is a group of
conjugacy class $2^5$ Type 2 in $\MM$. It clearly contains
the index 2 subgroup $V < T_1$. The remaining cases can
be easily verified by proving that all index 2 subgroups of $V$
are conjugates of this one.
"""

ρ.order() # 31
check_normalise(T1_basis, [ρ], group_set=T1_as_int) # True
check_normalise((z, z1, w, k4), [ρ]) # False

"""
It follows the action of $\rho$ generates $31 = 2^5 - 1$ conjugates of $V$ ---
and the Type II $2^5$ embedding it --- in $\tilde{E}$ (see next line of code),
as 31 is prime. But this is exactly the number of index 2 subgroups
of $T_1 \cong 2^5$!

With that settled, show the claimed generators belong
to the normaliser of $\tilde{E}$.
"""

check_normalise(L_E, (*L_N, ρ)) # True

"""
As for showing the entire normaliser is generated, consider three families of elements
in $\nm{\tilde{E}}$:
* the generators $\left( g_{10}, h_{10} \right)$, which (in particular) generate the $\orth+{10}{2}$;
"""

F1 = L_N

"""
* 7 generators of the projection of $\cm{\tilde{E}} < \GG$ into $\CO$;
"""

B = (g10*h10)**21
F2 = (B, B**h10, B**(h10**2), B**(h10**3), B**(h10*g10*h10**2), B**(h10**2*g10*h10**2), B**(h10**5), B**(h10**4*g10*h10))

"""
* and 20 generators of $\QQ \cap \cm{\tilde{E}}$.
"""

F3 = [F2[6]*F2[7]*B**(h10*g10*h10**4)/(F2[2]*F2[4]), B**(h10**4), B**(h10**3*g10*h10), B**(h10*g10*h10**3), B**((h10*g10*h10)**2), B**(h10**2*(g10*h10)**3), B**(h10**2*g10*h10*g10*h10**5), B**(h10*g10*h10**6), F2[0]*F2[2]*F2[0]/F2[2], F2[1]*F2[5]*F2[1]/F2[5], F2[2]*F2[5]*F2[2]/F2[5], F2[3]*F2[5]*F2[3]/F2[5], F2[0]*F2[6]*F2[0]/F2[6], F2[3]*F2[6]*F2[3]/F2[6], F2[3]*F2[7]*F2[3]/F2[7], F2[4]*B**(h10**7)*F2[4]/B**(h10**7)]

"""
First, show $\langle g_{10}, h_{10} \rangle$ act on $\tilde{E}$
as standard generators of the $\orth+{10}{2}$, while members of the other 3 families act trivially.

It suffices to test the images of generators of $\tilde{E}$ under the action,
as the conjugation action is an automorphism on $\tilde{E}$.
"""

act_on_e = lambda g: tuple(as_int(x**g) for x in L_E)
size_image((*F2, *F3), act_on_e) # 1
size_image([g10*h10**2], act_on_e) # 17
size_image([(g10*h10**7)**2], act_on_e) # 31

"""
Since a check on the online ATLAS shows no maximal subgroup of $\orth+{10}{2}$
has order divisible by both 17 and 31, $g_{10}$ and $h_{10}$ are generators thereof.

Furthermore, introduce 3 elements of $\tilde{E}$, one of which projects
to an element of order 60 in $\orth+{10}{2}$:
"""

x60 = MM("M<y_196h*x_158bh*d_0a3dh*p_44870370*l_1*p_57699840*t_1>")
r = MM("M<y_12h*x_16d0h*d_893h*p_194072911*l_1*p_971520*t_1*l_1*p_2880*l_1*p_11704944*t_2>")
s = MM("M<y_5a4h*x_1679h*d_0d57h*p_9427896*t_1*l_1*p_3384960*l_2*t_1*l_1*p_2373120>")
check_normalise(L_E, (x60, r, s)) # True

size_image([x60], act_on_e) # 60

"""
The action of $x_{60}$ on $U$ thus has order 60. The GAP character table library
reveals all elements of order 60 in $\orth+{10}{2}$ have 3^rd powers in conjugacy class 20A
and thus 30^th powers in 2A, so checking
"""

g10 == (x60**30)**r # True
h10 == (x60**3)**s # True
size_image([g10*h10], act_on_e) # 21

"""
ensures $g_{10}$ projects to an element in class 2A, $h_{10}$ to one in class 20A,
and $g_{10}h_{10}$ to an element of order 21. This makes the actions of
$g_{10}$, $h_{10}$ standard generators for the $\orth+{10}{2}$.

Now, verifying that all elements of $\mathcal{F}_2$ and
$\mathcal{F}_3$ do indeed lie in $\GG = \QQ.\CO$ ...
"""

all(x.in_G_x0() for x in (*F2, *F3)) # True

"""
show that $\mathcal{F}_2$ generates $2^9$ cosets of $\QQ$ in $\GG$.
"""

size_image(F2, to_co1) # 512

"""
Finally, verify that $\mathcal{F}_3$ generates a subgroup of $\QQ$
with order $2^{17}$. Note the second element of the output is `True`, so that
the result is trustworthy.
"""

dim_q(F3) # (17, True)

"""
In summary, it is possible to find in $\langle g_{10}, h_{10} \rangle \le \nm{\tilde{E}}$:
* $2^{17}$ elements of $\QQ$, all of which act trivially on $\tilde{E}$;
* $2^9$ elements of $\GG = \QQ.\CO$ which lie in distinct cosets of $\QQ$,
all of which act trivially on $\tilde{E}$;
* $\left| \orth+{10}{2} \right|$ elements which act differently on $\tilde{E}$.

It follows $\left| \langle g_{10}, h_{10} \rangle \right| \ge 2^{17} \cdot 2^{9}
\left| \orth+{10}{2} \right| = \left| 2^{10+16} \udot \orth+{10}{2} \right|$,
so that $\langle g_{10}, h_{10} \rangle = \nm{\tilde{E}}$.
"""


"""
# $\alt{5}$ in the Monster <a id="lemma"></a>
We confirm the pairs of generators in `A5_dict` generate $\alt{5}$s of
the appropriate types.

First, verify that each pair consists of non-trivial elements satisfying
the presentation $\langle a, b \mid a^2, b^3, \left( ab \right)^5 \rangle$
for $\alt{5}$. Since $\alt{5}$ is simple, it follows by Von Dyck's theorem
that they generate groups isomorphic to it.
"""

all(g2.order() == 2 and g3.order() == 3 and (g2*g3).order() == 5 for g2, g3 in A5_dict.values()) # True

"""
With the shape of the groups established, now confirm that their elements
of orders 2, 3, and 5 fuse to the correct conjugacy classes of the Monster.
Since $\alt{5}$ contains unique conjugacy classes of elements
with each of these orders, it is enough to confirm that $\chi_\MM$ values of
(suitable conjugates of) the generators and their products correspond
to the correct $\MM$-classes.
"""

g2_AAA, g3_AAA = A5_dict["AAA"]
g2_AAA.in_G_x0() and g3_AAA.in_G_x0() # True
g2_AAA.chi_G_x0()[0] # 4371
g3_AAA.chi_G_x0()[0] # 782
(g2_AAA*g3_AAA).chi_G_x0()[0] # 133

g2_BAA, g3_BAA = A5_dict["BAA"]
g2_BAA.in_G_x0() and g3_BAA.in_G_x0() # True
g2_BAA.chi_G_x0()[0] # 275
g3_BAA.chi_G_x0()[0] # 782
(g2_BAA*g3_BAA).chi_G_x0()[0] # 133

g2_BBA, g3_BBA = A5_dict["BBA"]

# The following elements conjugate g3_BBA, g2_BBA*g3_BBA into G_x0
c = MM("M<y_0ch*x_184h*d_4b4h*p_44816786*l_2*p_3840*l_2*p_2112*l_2*p_10267200*t_1*l_1*p_35520*l_2*t_2*l_1*p_2937600*t_1*l_2*p_2386560*l_2*p_42753057*t_2>")
d = MM("M<y_48eh*x_3f5h*d_698h*p_145537752*l_2*p_49272960*l_1*p_140638080*l_2*t_1*l_2*p_960*l_2*p_10665888*l_2*p_1142400*t_2*l_2*p_59030400*l_1*p_200069808*l_1*t_2*l_1*p_4012800*t_2*l_2*p_1943040*l_2*p_53459098*t_1*l_2*p_1985280*l_1*p_21364949*t_1*l_2*p_63909120>")
g3_conj, g5_conj = g3_BBA**c, (g2_BBA*g3_BBA)**d
g3_conj.in_G_x0() and g5_conj.in_G_x0() # True

g2_BBA.conjugate_involution()[0] # 2
g3_conj.chi_G_x0()[0] # 53
g5_conj.chi_G_x0()[0] # 133

g2_ACA, g3_ACA = A5_dict["ACA"]
g2_ACA.in_G_x0() and g3_ACA.in_G_x0() # True
g2_ACA.chi_G_x0()[0] # 4371
g3_ACA.chi_G_x0()[0] # -1
(g2_ACA*g3_ACA).chi_G_x0()[0] # 133

g2_BCA, g3_BCA = A5_dict["BCA"]
g2_BCA.in_G_x0() and g3_BCA.in_G_x0() # True
g2_BCA.chi_G_x0()[0] # 275
g3_BCA.chi_G_x0()[0] # -1
(g2_BCA*g3_BCA).chi_G_x0()[0] # 133

g2_BCB, g3_BCB = A5_dict["BCB"]
g2_BCB.in_G_x0() and g3_BCB.in_G_x0() # True
g2_BCB.chi_G_x0()[0] # 275
g3_BCB.chi_G_x0()[0] # -1
(g2_BCB*g3_BCB).chi_G_x0()[0] # 8

g2_B, g3_B = A5_dict["B"]
g2_T, g3_T = A5_dict["T"]

# The following elements (from Pisani and Popiel) conjugate g3_B, g2_B*g3_B into G_x0
c = MM("M<y_0adh*x_128h*d_9bh*p_152633473*l_2*p_60804480*l_1*p_243091248*l_2*t_1*l_1*p_68787840*l_1*p_212044848*l_1*t_2*l_1*p_1499520*l_1*p_32535003*l_1*t_1*l_1*p_2027520*l_1*p_11521*t_1*l_2*p_783360*t_2*l_2*p_2830080*l_2*p_86257556*t_1*l_2*p_1943040*l_2*p_96477752*t_1*l_2*p_2956800*l_1*p_43197549>")
d = MM("M<y_4f1h*x_9bch*d_0f77h*p_106507260*l_1*p_80762880*l_2*p_213375504*t_2*l_1*p_1499520*l_2*p_583047*t_2*l_2*p_1900800*l_2*p_1040998*t_2*l_2*p_2386560*l_2*p_21331401*t_1>")
g3_conj, g5_conj = g3_B**c, (g2_B*g3_B)**d
g3_conj.in_G_x0() and g5_conj.in_G_x0() # True

g2_B.conjugate_involution()[0] # 2
g3_conj.chi_G_x0()[0] # 53
g5_conj.chi_G_x0()[0] # 8

# The following elements conjugate g3_T, g2_T*g3_T into G_x0
c = MM("M<y_4fah*x_4e4h*d_0a09h*p_177449985*l_1*p_1920*l_2*p_2256*l_2*p_513600*t_2*l_1*p_9778560*l_2*p_127776000*t_2*l_1*p_1499520*l_1*p_43638176*t_2*l_1*p_2027520*l_1*p_10691751*l_1*t_2*l_1*p_1457280*l_2*p_1461619>")
d = MM("M<y_0c0h*x_4bbh*d_7bfh*p_222689108*l_1*p_3840*l_2*p_465936*l_2*p_6106560*t_1*l_1*p_2494080*l_1*t_2*l_1*p_2325120*t_2*l_2*p_1985280*l_1*p_21368810*t_2>")
g3_conj, g5_conj = g3_T**c, (g2_T*g3_T)**d
g3_conj.in_G_x0() and g5_conj.in_G_x0() # True

g2_T.conjugate_involution()[0] # 2
g3_conj.chi_G_x0()[0] # 53
g5_conj.chi_G_x0()[0] # 8

"""
This completes the proof for all except the type B and T subgroups $\alt{5}$,
which cannot be distinguished on the basis of its class fusions alone. Show
that the normaliser of the former contains an element of $y_4$ of
order 4 such that $y_4^2 \notin \langle g_{2B}, g_{3B} \rangle$, which is
not the case for the normaliser $\sym{5} \times \sym{3}$ of a type T $\alt{5}$,
and that the centraliser of the latter contains $y_3 \in \MM$ of order 3,
unlike the centraliser 2 of a type B $\alt{5}$:
"""

y3 = MM("M<y_714h*x_593h*d_6dh*p_225335367*l_1*p_1415040*l_2*p_22416*l_1*p_1974720>")
y3.order() # 3
g2_T*y3 == y3*g2_T # True
g3_T*y3 == y3*g3_T # True

# The following element comes from Pisani and Popiel
y4 = MM("M<y_163h*x_1c92h*d_608h*p_59179108*l_1*p_2999040*l_1*p_43617991*t_1*l_2*p_2880*l_2*p_2160*l_2*p_2369280*t_2*l_2*p_1457280*l_1*p_1860708*l_2*t_2*l_2*p_2386560*l_2*p_85819731*t_1*l_2*p_1943040*l_2*p_42707029*t_2*l_2*p_2386560*l_2*p_21439072*t_1*l_1*p_1457280*l_2*p_10566>")
y4.order() # 4
g2_B*y4 == y4*g2_B # True
g3_B**y4 == g2_B*g3_B**2*g2_B*g3_B*g2_B*g3_B**2 # True
g3_B**(y4**2) == g3_B # True

"""
Since $y_4^2$ centralises $\langle g_{2B}, g_{3B} \rangle \cong \alt{5}$
(indeed, $y_4$ itself commutes with $g_{2B}$), a group
with trivial centre, $y_4^2 \notin \langle g_{2B}, g_{3B} \rangle$.
"""

"""
# Projective Linear Groups

## $\psl{2}{71}$ <a id="psl2_71"></a>
Generators are given by:
"""

g71 = MM("M<y_3b5h*x_1d10h*d_0b5ch*p_212508477*l_2*p_1920*l_2*p_22272*l_2*p_495360*t_2*l_1*p_465600*l_2*p_1521072*l_2*t_2*l_2*p_2787840*l_2*p_21873173*l_2*t_2*l_2*p_1900800*l_2*p_11554*t_2*l_2*p_2830080*l_2*p_64086265*t_1*l_2*p_1985280*l_1*p_53804514*t_2*l_1*p_1394880*l_2*p_43255296*t_2*l_2*p_2386560*l_2*p_96463249>")
h71 = MM("M<y_95h*x_416h*d_7ech*p_164312929*l_1*p_2640000*l_1*p_467830*t_2*l_2*p_1858560*l_1*p_33391008*l_2*t_2*l_1*p_1457280*l_2*p_21873077*l_1*t_2*l_1*p_2115840*l_1*t_2*l_2*p_1943040*l_2*p_10799414*t_2*l_2*p_2597760*l_1*p_85416595*t_2*l_2*p_1858560*l_1*p_128112*t_1*l_2*p_2386560*l_2*p_64001593>")

"""
Since this is a simple group embedded uniquely up to conjugacy in $\MM$, it suffices
to confirm that the above elements generate a group isomorphism to $\psl{2}{71}$.
"""

test_xsl(g71, h71, 71) # True

"""
Although unnecessary, it is also easy to verify that this group contains
a B-type $\alt{5}$ in agreement with Holmes and Wilson.
"""

g2_B, g3_B = A5_dict["B"]
g71*h71 == g3_B # True
h71**(g71*h71*g71**5*(h71*g71**3)**2*g71) == g2_B # True

"""
## $\psl{2}{41}$ <a id="psl2_41"></a>
Generators are given by:
"""

g41 = MM("M<y_106h*x_0abbh*d_0f89h*p_232234994*l_2*p_2597760*l_1*p_1107499*t_1*l_2*p_1900800*l_2*p_12128135*l_1*t_1*l_1*p_1393920*l_1*p_10668816*l_1*p_2517120*t_1*l_2*p_1943040*l_2*p_11247744*t_2*l_1*p_1415040*l_2*p_465936*l_1*p_2578560*t_2*l_2*p_2386560*l_2*p_42736709*t_2*l_1*p_1499520*l_2*p_96456658>")
h41 = MM("M<y_12ch*x_17d8h*d_743h*p_14762554*l_2*p_1900800*l_2*p_12556439*t_2*l_2*p_2787840*l_2*p_11730776*l_1*t_2*l_2*p_2787840*l_2*p_22751364*l_1*t_2*l_2*p_2344320*l_2*p_152071*t_1*l_2*p_1943040*l_2*p_85413717*t_1*l_2*p_1943040*l_2*p_53436230*t_1*l_2*p_2830080*l_2*p_53907457>")

"""
Since this is a simple group embedded uniquely up to conjugacy in $\MM$, it suffices
to confirm that the above elements generate a group isomorphism to $\psl{2}{41}$.
"""

test_xsl(g41, h41, 41) # True

"""
Although unnecessary, it is also easy to verify that this group contains
a B-type $\alt{5}$ in agreement with Holmes and Wilson.
"""

g2_B, g3_B = A5_dict["B"]
g41*h41 == g3_B # True
h41**(g41**5*h41*g41**2) == g2_B # True

"""
## $\pgl{2}{29}$ <a id="pgl2_29"></a>
Note that Dietrich et al. have previously provided a substantially similar construction and proof;
however, the following was obtained independently.

Generators are
"""

g29 = MM("M<y_458h*x_146bh*d_7bbh*p_10221541*l_2*p_2787840*l_2*p_971712*t_1*l_2*p_2386560*l_2*p_29955*l_1*t_1*l_2*p_2597760*l_1*p_22310016*l_2*t_1*l_2*p_1943040*l_2*p_85329042*t_1*l_1*p_2640000*l_1*p_255959*t_1*l_2*p_1858560*l_1*p_10668720*l_2*p_1044480*t_2*l_1*p_1930560*l_1*t_2*l_1*p_68344320*l_1*p_243978336>")
h29 = MM("M<y_1d6h*x_1077h*d_0f7dh*p_242733094*l_2*p_1457280*l_1*p_28995*t_2*l_2*p_2787840*l_2*p_33417088*l_1*t_1*l_1*p_1394880*l_2*p_23232*l_1*p_980160*t_2*l_1*p_1457280*l_2*p_1026641*t_1*l_2*p_1985280*l_1*p_64084336*t_2*l_2*p_2956800*l_1*p_170654226*t_1*l_2*p_2597760*l_1*p_106698926>")

"""
It suffices to verify we have a subgroup of the correct structure,
as these form a unique conjugacy class of subgroups (which are maximal).
To this end, employ test_pgl.
"""

test_pgl(g29, h29, 29) # True

"""
This completes the proof. For verification's sake,
show the group contains a B-type $\alt{5}$ in agreement
with Holmes and Wilson.
"""

g2_B, g3_B = A5_dict["B"]
(g29*h29**2)**2 == g2_B # True
g29*h29*g29*h29**3*(g29*h29)**2*g29*h29**3*g29*h29**8*(g29*h29)**2 == g3_B # True

"""
## $\pgl{2}{19}$ <a id="pgl2_19"></a>
The following proof is adapted from Pisani and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

Generators are
"""

x2 = MM("M<y_531h*x_147bh*d_9e6h*p_236396641*l_2*p_1985280*l_1*p_21825835*l_1*t_2*l_1*p_1499520*l_2*p_32991824*l_2*t_2*l_2*p_1415040*l_1*p_24192*l_2*p_2496960*t_1*l_1*p_1499520*l_1*p_12113794*t_1*l_1*p_2027520*l_1*p_86261393*l_2*p_11594880*t_2*l_1*p_1394880*l_2*p_465792*l_1*p_2392320>")
x19 = MM("M<y_7ddh*x_0e39h*d_99h*p_136245180*l_1*p_1499520*l_1*p_23222870*t_1*l_1*p_1499520*l_2*p_1925316*l_1*t_2*l_1*p_2640000*l_1*p_1504850*l_1*t_1*l_2*p_2830080*l_2*p_127990691*t_1*l_2*p_1457280*l_1*p_175110*t_1*l_1*p_1920*l_2*p_10667712*l_2*p_6106560*t_1*l_2*p_2386560*l_2*p_42663561*t_2*l_2*p_2597760*l_1*p_85812125>")

"""
Check that $x_2$ and $x_{19}$ satisfy the presentation of
Robertson and Williams for $\pgl{2}{19}$, and that $x_{19}$ has
an order (namely, 19) not found in any proper factor group.
"""

test_pgl(x2, x19, 19) # True

"""
It follows that $\langle x_2, x_{19} \rangle \cong \pgl{2}{19}$, and
thus by Holmes and Wilson that it is maximal in $\MM$ iff it contains
a B-type $\alt{5}$.

Confirm that certain elements of $\langle x_2, x_{19} \rangle$ coincide
with the generators of the known type-B $\alt{5} < \MM$ defined
in [Lemma 4.1](#lemma).
"""

g2_B, g3_B = A5_dict["B"]
g2_B == (x19**2*x2)**2 # True
g3_B == x2*x19**2*x2*x19 # True

"""
## $\pgl{2}{13}$ <a id="pgl2_13"></a>
The following proof is adapted from Dietrich, Lee, and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

Generators are $g_{13}$ in the the proof for the 13A normaliser and
"""

u = MM("M<y_438h*x_0f05h*d_6ebh*p_127839018*l_2*p_1985280*l_1*p_23241243*t_2*l_1*p_2027520*l_1*p_474375*l_1*t_2*l_2*p_2787840*l_2*p_32068420*l_1*t_2*l_2*p_1457280*l_1*p_9635*t_2*l_1*p_1499520*l_1*p_42675112*t_1*l_1*p_1457280*l_2*p_43178339*l_1*t_2*l_1*p_1920*l_2*p_3120*l_2*p_5180160>")
g13 = MM("M<y_519h*x_0cb8h*d_3abh*p_178084032*l_2*p_2344320*l_2*p_471482*l_1*t_1*l_2*p_2830080*l_2*p_22371347*l_2*t_2*l_1*p_1499520*l_2*p_22779365*l_2*t_1*l_2*p_2597760*l_1*p_11179396*t_1*l_1*p_1499520*l_2*p_85838017*t_2*l_1*p_1499520*l_1*p_64024721*t_2*l_2*p_2386560*l_2*p_21335269>")

"""
Note that $g_{13}$ is as in [Theorem 2.24](#norm13A).  
Check $u$ and $g_{13}$ generate a group of structure $\pgl{2}(13)$.
"""

test_pgl(u, g13, 13) # True

"""
As for maximality, the results of Norton (1998) in conjunction with those of Dietrich et al.
show there are three conjugacy classes of $\psl{2}{13}$ (not PGL!) in the Monster.
The two classes which do not extend to maximal $\pgl{2}{13}$s are centralised by elements
of order 3, whereas the third is not. Hence, exhibit elements of $\langle u, g_{13}$
generating a subgroup $\psl{2}{13}$:
"""

x2 = (u*g13**2)**2
test_xsl(g13, x2, 13) # True

"""
It follows that $\langle g_{13}, x_2 \rangle \cong \psl{2}{13}$. Now,
the centraliser of this group is a subgroup of $\cm{g_{13}}$,
which belongs inside the group $\nm{g_{13}} \cong \left( 13{:}6 \times \psl{3}{3} \right) \udot 2$
constructed in [Theorem 2.24](#norm13A). Recalling that the factor
$13{:}6$ is generated by $g_{13}$ and an element $y_{12}^2$,
observe the following:
"""

# The element y12 mentioned
y12 = MM("M<y_5c4h*x_0d78h*d_0ce0h*p_190945267*l_2*p_2344320*l_2*p_32475110*l_1*t_2*l_2*p_2597760*l_1*p_12134921*l_1*t_2*l_1*p_2880*l_2*p_3216*l_2*p_5180160*t_2*l_2*p_2787840*l_2*p_216480*t_2*l_2*p_2830080*l_2*p_42756901*t_1*l_2*p_1985280*l_1*p_11152936*t_1*l_2*p_2956800*l_1*p_85840900>")

# The following is x6 = g6/y6 of Dietrich et al.
x6 = y12**-2*1/g13*x2*g13**7*x2*g13**2*x2
x6**(y12**2) == x6 # True
g13**x6 == g13 # True
x6.order() # 6

"""
We may thus write $g_{13}^{-1} x_2 g_{13}^7 x_2 g_{13}^2 x_2 \in
    \langle g_{13}, x_2 \rangle$ as $y_{12}^2 x_6$
for some $x_6 \in \cma{g_{13}, y_{12}^2} \cong \psl{2}{13}$. Any element of
$\cm{g_{13}} < \langle g_{13}, y_{12}^2 \rangle \times \cma{g_{13}, y_{12}^2}$
commutes with this element if and only if it commutes with both $y_{12}^2$ and
$x_6$, however, so that $\cma{g_{13}, x_2}$ is a subgroup of
$\cma{g_{13}, y_{12}^2}$ centralising $x_6$. Data
in the GAP character table library show elements of order 6 in $\psl{2}{13}$
generate their own centralisers, limiting the possibilities for elements of order
3 possibly commuting with $\langle g_{13}, x_2 \rangle$ to powers of $x_6^2$.
"""

x2**(x6**3) == x2 # False

"""
By the above, this guarantees $\langle u, g_{13} \rangle$ is maximal.
Indeed, although unnecessary, it can easily be shown that $\langle g_{13}, x_2 \rangle$
has trivial centraliser by verifying $x_6^2$ does not commute with $x_2$:
"""

x2**(x6**2) == x2 # False


"""
## $\psl{2}{59}$ <a id="psl2_59"></a>
There is no subgroup of the Monster with this shape! The proof is essentially
identical to Holmes and Wilson's 2002 construction of such a subgroup, except
(of course) for the eventual negative result.

Suppose to the contrary that $G \cong \psl{2}{59} < \MM$. Constructing
a model of $\psl{2}{59}$ in GAP, one can verify that groups of this shape
have (maximal) subgroups $\alt{5}$ and that the normalisers of elements of
order 5 have shape $\dih{60} \cong 2 \times \dih{30}$. Furthermore, Norton and
Wilson (2002) prove that the elements of order 2, 3, and 5 in $G$ must lie
in $\MM$-classes 2B, 3B, and 5B, respectively. It follows $G$ has a subgroup
$\alt{5}$ of type B or T; replacing $G$ with a suitable conjugate as necessary,
we may take this to be a fixed $\alt{5}$ for each type. Referring to the elements
in [Lemma 4.1](#lemma), let these be $\langle g_{2T}, g_{3T} \rangle$ and
a conjugate of $\langle g_{2B}, g_{3B} \rangle$ such that their intersection
is $\langle z, g_{2T} g_{3T} \rangle \cong \dih{10}$:
"""

g2_B, g3_B = A5_dict["B"]
c = MM("M<y_42fh*x_1e9bh*d_0bc1h*p_55207716*l_2*p_1943040*l_2*p_1461488*l_2*t_1*l_1*p_2999040*l_1*p_21798955*l_2*t_2*l_1*p_2640000*l_1*p_21912468*l_1*t_2*l_2*p_1900800*l_2*p_5768*t_2*l_2*p_1943040*l_2*p_42727137*t_1*l_2*p_2830080*l_2*p_21544935*t_2*l_1*p_1457280*l_2*p_1121811*t_1*l_2*p_2386560*l_2*p_64023715>")
b2 = g2_B**c
b3 = g3_B**c
b5 = b2*b3

g2_T, g3_T = A5_dict["T"]
g2_T*g3_T == b5 # True
g2_T**(g3_T*g2_T*g3_T**2) == b2**(b3*b2*b3**2) == z # True
b5**z == 1/b5 # True

"""
Since $z$ is an involution and $g_{2T} g_{3T}$ has order 5, this last statement
confirms $\langle z, g_{2T} g_{3T} \rangle \cong \dih{10}$.

Now, recall that the elements of order 5 in $G$ have normalisers
$2 \times \dih{30}$. Any $\dih{10} < G$ --- which normalises its elements of
order 5 and has a trivial center --- is thus centralised by an involution
of $G$, all of which belong to conjugacy class 2B of the Monster.
The centraliser of $\dih{10} < \alt{5}$ has structure
$5^3.\left( 4 \times \alt{5} \right)$ for a type B or T $\alt{5}$ (Norton 1998).
Hence, to show that the following elements generate $\cma{z, g_{2T} g_{3T}}$,
it is enough to confirm that they generate a subgroup of order at least
$\left| 5^3.\left( 4 \times \alt{5} \right) \right| =
    5^3 \cdot 4 \left| \alt{5} \right| = 30\,000$.
"""

cgens = (
    MM("M<y_3c8h*x_0fa8h*d_220h*p_128332441*l_1*p_2027520*l_1*p_1423899>"),
    MM("M<y_1ech*x_0e8dh*d_4eeh*p_10929978*l_1*p_1858560*l_1*p_10667856*l_2*p_3826560>"),
    MM("M<y_2bah*x_0fcch*d_249h*p_99573767*l_2*p_1943040*l_2*p_11165001*l_1>"),
    MM("M<y_3b2h*x_1515h*d_6d8h*p_207805390*l_1*p_3840*l_1*p_4080*l_1*p_10478400>"),
    MM("M<y_773h*x_13adh*d_0e77h*p_49947306*l_2*p_2787840*l_2*p_32974529*l_1>"),
    MM("M<y_131h*x_0ceeh*d_0c28h*p_44752564*l_1*p_2640000*l_1*p_221312>")
)

# To show x commutes with z, show it lies in C_M(z) = G_x0
all(x.in_G_x0() for x in cgens) # True
all(x**b5 == x for x in cgens) # True

# Keep a record of known element images under as_int, as well any 2B involutions
seen = set()
involutions = []

power_lists = [[x**i for i in range(k)] for x, k in zip(cgens, (5, 5, 5, 4))]
the_a5 = size_image(cgens[-2:], return_type=list)
for l0 in power_lists[0]:
    for l1 in power_lists[1]:
        xl1 = l0*l1
        for l2 in power_lists[2]:
            xl2 = xl1*l2
            for l3 in power_lists[3]:
                xl3 = xl2*l3
                for l4 in the_a5:
                    xl4 = xl3*l4
                    k = as_int(xl4)
                    if k not in seen:
                        seen.add(k)
                        if xl4.order(2) == 2 and xl4.chi_G_x0()[0] == 275:
                            involutions.append(xl4)
                    
                    print(len(seen), len(involutions), end="\r")

len(seen) # 30000

"""
The aforementioned observations indicate $G$ contains a 2B involution
in this group, regardless of whether it contains our type B or T $\alt{5}$
(or both). All such elements were found while enumerating $\cm{\dih{10}}$;
confirm that there are exactly 500, in agreement with Holmes and Wilson.
"""

len(involutions) # 500

"""
Referring again to a model of $\psl{2}{59}$ in GAP, or to the group's character
table, one finds an element thereof must have order 1, 2, 3, 5, 6, 10, 15, 29,
30, 59. Tests of the orders of various elements in the groups generated
by the chosen type B or T $\alt{5}$ and each candidate involution reveal
that none can satisfy this criterion, however, for the desired contradiction.
"""

orders = {1, 2, 3, 5, 6, 10, 15, 29, 30, 59}

# All orders are less than 60, so we can set that as an upper bound
beta1 = (b2**(b3*b2)).reduce()
b_involutions_1 = [x for x in involutions if (x*beta1).order(60) in orders]
b_involutions_2 = [x for x in b_involutions_1 if (x*b3).order(60) in orders]
any((b2*x*b3).order(60) in orders for x in b_involutions_2) # False

theta1 = (g2_T**(g3_T*g2_T)).reduce()
t_involutions_1 = [x for x in involutions if (x*theta1).order(60) in orders]
any((g2_T*x*g3_T).order(60) in orders for x in t_involutions_1) # False

"""
# The Non-Local Subgroups

## $\left( \alt{5} \times \alt{12} \right){:}2$ <a id="normAAA"></a>
The following proof is adapted from one provided for the index 2 subgroup
$\alt{5} \times \alt{12}$ by Dietrich, Lee, and Popiel. This construction
merely extends that group with the element $n$.

****

Generators are
"""

gAAA = MM("M<y_489h*x_1ea3h*d_7c4h*p_37889982*l_1*p_2027520*l_1*p_22303057*t_1*l_2*p_2956800*l_1*p_33454518*l_2*t_2*l_2*p_2787840*l_2*p_10677187*l_1*t_1*l_1*p_1499520*l_2*p_42747504*t_2*l_2*p_1457280*l_1*p_22793737*l_2*t_2*l_1*p_1499520*l_1*p_42714645*t_2*l_2*p_2386560*l_2*p_53803593>")
hAAA = MM("M<y_781h*x_6dbh*d_7b6h*p_126867354*l_1*p_1457280*l_2*p_53462968*t_2*l_2*p_1900800*l_2*p_11729813*l_2*t_2*l_1*p_2999040*l_1*p_11596960*l_1*t_1*l_2*p_2787840*l_2*p_33398833*l_2*t_1*l_1*p_2640000*l_1*p_6724*t_1*l_2*p_1943040*l_2*p_53885345>")
n = MM("M<y_1bh*x_1a5fh*d_753h*p_229948825*l_2*p_2830080*l_2*p_23202565*l_2>")
L_N = (gAAA, hAAA, n)

"""
This subgroup is the normaliser of a type AAA $\alt{5}$, in this case the one
exhibited in [Lemma 4.1](#lemma):
"""

L_E = g2_AAA, g3_AAA = A5_dict["AAA"]

"""
To show as much, first check that $g_{2AAA}, g_{3AAA}$ lie in the group.
"""

g2_AAA == gAAA**3 # True
g3_AAA == hAAA**10 # True

"""
Now define elements $x_3, x_{10} \in \langle g_{2AAA}, g_{3AAA} \rangle$
which commute with $\langle g_{2AAA}, g_{3AAA} \rangle$.
"""

x3 = gAAA*g2_AAA
x10 = hAAA/g3_AAA
all(x*y == y*x for x in (x3, x10) for y in L_E) # True

"""
Since $x_3, x_{10}$ commute with $g_{2AAA}, g_{3AAA}$ (as will be checked
below), an immediate consequence is that $g_{AAA} = x_3 g_{2AAA}^{-1}$ and
$h_{AAA} = x_{10} g_{3AAA}$ belong to $\nma{g_{2AAA}, g_{3AAA}}$. Confirm
that $n$ does too by showing it centralises $g_{2AAA}$ and acts on $g_{3AAA}$
in such a way as to induce an outer automorphism of $\alt{5}$:
"""

g2_AAA*n == n*g2_AAA # True
A5_AAA = size_image(L_E, as_int, list)
a2_centraliser = [x for x in A5_AAA if g2_AAA*x == x*g2_AAA]

g3_AAA**n in A5_AAA # True
as_int(g3_AAA**n) in {as_int(g3_AAA**x) for x in a2_centraliser} # False

"""
Then verify the claim that $\langle x_3, x_{10} \rangle$ is an $\alt{12}$
commuting with the $\alt{5}$ generated by $g_{2AAA}, g_{3AAA}$. It satisfies
the appropriate presentation given by Coxeter and Moser:
"""

# That x3, x10 commute with g2_AAA, g3_AAA was checked above
x3**3 == x10**10 == (x3*x10)**11 == e # True
comm(x3, x10)**2 == (x3*x10**-2*x3*x10**2)**2 == e # True
comm(x3, x10**3)**2 == (x3*x10**-4*x3*x10**4)**2 == e # True
comm(x3, x10**5)**2 == e # True

"""
Having already shown $n$ induces an outer automorphism of
$\langle g_{2AAA}, g_{3AAA} \rangle$, it follows that $n$ lies
in the part of the $\alt{5}$ normaliser outside
the $\alt{5} \times  \alt{12}$, giving the entire $\left( \alt{5} \times \alt{12} \right){:}2$.
"""

"""
## $\left( \alt{6} \times \alt{6} \times \alt{6} \right).\left( 2 \times \sym{4} \right)$ <a id="normA6_3"></a>

Generators are given by
"""

gA6 = MM("M<y_29ah*x_72dh*d_0fe7h*p_107290399*l_1*p_3804480*l_1*t_1*l_2*p_1985280*l_1*p_13043028*l_2*t_1*l_2*p_1394880*l_1*p_465888*l_2*p_2819520*t_1*l_1*p_1499520*l_1*p_53350483*t_1*l_2*p_1985280*l_1*p_85371363*t_1*l_2*p_1943040*l_2*p_53799666*t_2*l_1*p_1457280*l_2*p_137696>")
hA6 = MM("M<y_41bh*x_0c52h*d_7d1h*p_98208424*l_2*p_1900800*l_2*p_211811*t_2*l_1*p_2640000*l_1*p_470467*l_1*t_1*l_2*p_2386560*l_2*p_1908002*l_1*t_2*l_1*p_2027520*l_1*p_8658*t_1*l_2*p_1510080*t_1*l_1*p_1499520*l_1*p_85330976*t_2*l_1*p_1499520*l_2*p_64004474*t_2*l_1*p_18648960>")
L_N = (gA6, hA6)

"""
This subgroup is the normaliser of a direct product of three commuting $\alt{6}$s
containing type AAA subgroups $\alt{5}$. We claim that this particular instance
normalises $E = \langle U, U^t, U^{t^2} \rangle$,
where $U = \langle x_{A6}, y_{A6} \rangle$ with
"""

xA6 = MM("M<y_480h*x_0aafh*d_0c65h*p_239966010*l_2*p_2880*l_2*p_10667760*l_2*p_10248960*t_1*l_1*p_930240*t_2*l_2*p_2830080*l_2*p_85371379*t_1*l_2*p_2597760*l_1*p_85814001>")
yA6 = MM("M<y_4c3h*x_0ad4h*d_2b6h*p_132231952*l_2*p_2830080*l_2*p_32578086*t_2*l_2*p_171240960*t_1*l_2*p_1985280*l_1*p_64088162*t_1*l_1*p_1499520*l_1*p_96464227>")
L_U = (xA6, yA6)

t = gA6**4

"""
Confirm that $U$ contains the generators $g_{2AAA}, g_{3AAA}$ of
the type AAA $\alt{5}$ in [Lemma 4.1](#lemma), and also that
$x_{A6}, y_{A6} \in U$ satisfy Carmichael's presentation for $\alt{6}$
given in Coxeter and Moser.
"""

g2_AAA, g3_AAA = A5_dict["AAA"]
xA6*yA6*xA6*yA6**2*xA6**2 == g2_AAA # True
xA6*yA6**2*xA6**2*yA6*xA6 == g3_AAA # True

xA6.order() # 4
yA6.order() # 3
(xA6*yA6)**5 == comm(yA6, xA6)**2 == (yA6/xA6**2*yA6*xA6**2)**2 == e # True

"""
Since $\alt{6}$ is simple, this shows $U$ is a suitable $\alt{6}$.
Moreover, $U^t$ and $U^{t^2}$ being conjugate to $U$, it will follows that
their join $E$ has the normaliser sought upon verifying that
the subgroups commute.
"""

xA6*xA6**t == xA6**t*xA6 # True
xA6*yA6**t == yA6**t*xA6 # True
yA6*xA6**t == xA6**t*yA6 # True
yA6*yA6**t == yA6**t*yA6 # True
xA6*xA6**(t**2) == xA6**(t**2)*xA6 # True
xA6*yA6**(t**2) == yA6**(t**2)*xA6 # True
yA6*xA6**(t**2) == xA6**(t**2)*yA6 # True
yA6*yA6**(t**2) == yA6**(t**2)*yA6 # True
xA6**t*xA6**(t**2) == xA6**(t**2)*xA6**t # True
xA6**t*yA6**(t**2) == yA6**(t**2)*xA6**t # True
yA6**t*xA6**(t**2) == xA6**(t**2)*yA6**t # True
yA6**t*yA6**(t**2) == yA6**(t**2)*yA6**t # True

"""
As for $\langle g_{A6}, h_{A6} \rangle$ being the $\alt{6}^3$ normaliser,
demonstrate that the conjugates of $x_{A6}$, $y_{A6}$,
$x_{A6}^t$, $y_{A6}^t$, $x_{A6}^{t^2}$, and $y_{A6}^{t^2}$ by $g_{A6}, h_{A6}$
fall in $U^{t^i}$ for some $0 \le i \le 2$.
"""

# Note t has order 3, so that x is in U^(t^k) iff x^(t^(3-k)) is in U
t**3 == e # True

xA6**(gA6*t**2) == xA6**(t**2*gA6) == xA6**(t*gA6*t) == xA6*yA6**2*xA6**2*yA6 # True
yA6**(gA6*t**2) == yA6**(t**2*gA6) == yA6**(t*gA6*t) == xA6**3*yA6**2*xA6*yA6*xA6*yA6**2 # True
xA6**hA6 == yA6**2*xA6**3*yA6 # True
yA6**hA6 == yA6 # True
xA6**(t*hA6*t) == yA6*xA6*yA6**2 # True
yA6**(t*hA6*t) == yA6*xA6*yA6*xA6**3*yA6**2 # True
xA6**(t**2*hA6*t**2) == (yA6*xA6)**2*yA6**2*xA6*yA6 # True
yA6**(t**2*hA6*t**2) == (yA6*xA6)**3*xA6*yA6*xA6 # True

"""
Hence $g_{A6}, h_{A6} \in \nm{U, U^t, U^{t^2}}$ --- note that they in fact
permute the three conjugates of $U$. To now prove that they generate
the normaliser of shape $\left( \alt{6} \times \alt{6} \times \alt{6} \right).\left( 2 \times \sym{4} \right)$, begin by exhibiting words
for $x_{A6}$, $y_{A6}$, and $t$:
"""

(gA6**3*hA6**2)**10 == xA6 # True
hA6**4 == yA6 # True
# t is gA6^4 by definition

"""
This accounts for $\langle U, U^t, U^{t^2} \rangle$ itself, along with $t$
(to be used later). We account for factor group $2 \times \sym{4}$ in stages.
Start with an element which induces an outer automorphism of $U$ and
centralises $U^t$.  
Observe (e.g. from the GAP Character Table Library) that elements of order 4
in $\alt{6}$ are self-centralising. Conjugation by the following element
fixes $x_{A6}, x_{A6}^t, y_{A6}^t$ and takes $y_{A6}^t$ to $y_{A6}^{-1} \notin
    y_{A6}^{\langle x_{A6} \rangle}$ for the desired result.
(One necessarily has $y_{A6}^{c_0} \in U$ if $x_{A6}^{c_0} \in U$
and similarly for $y_{A6}$, as $c_0 \in \langle g_{A6}, h_{A6} \rangle$
permutes $U, U^t, U^{t^2}$).
"""

c0 = (gA6**3*hA6**2*gA6*hA6**3)**6
c0.order() # 2
all(x**c0 == x for x in (xA6, xA6**t, yA6**t)) # True
yorb = [yA6**(xA6**i) for i in range(4)]
 # For efficiency
yorbset = {as_int(x) for x in yorb}
as_int(1/yA6) in yorbset # False

"""
Since no element of $\langle U, U^t, U^{t^2} \rangle \cong \alt{6}^3$ can induce
an outer automorphism of $U^t$, Lemma 2.1 shows addition of $\langle E, c_0 \rangle$
is at least twice as large as $E$. The same argument applies in turn
to $c_1$ below, which induces an outer automorphism of $U^t$ while centralising $U$:
"""

c1 = (hA6**2*gA6**3*hA6**3)**6
all(x**c1 == x for x in (xA6, yA6, xA6**t)) # True
as_int(yA6**(t*c1/t)) in yorbset # False

"""
For a third factor of 2, we exhibit an element $c_2$ which normalises $U^t$
while inducing an outer automorphism of $U$ not accounted for by introducing
$c_0$. Note that $c_0$, as an involution which normalises
$\langle x_{A6}, y_{A6} \rangle$, extends it to a group
$\langle x_{A6}, y_{A6}, c_0 \rangle$ twice as large with the original
as a normal subgroup. The centraliser of $x_{A6}$ is then $\langle x_{A6} \rangle
    \cup \langle x_{A6} \rangle c_0$ --- recall $c_0$ commutes with $x_{A6}$.
"""

c2 = gA6**3/yA6
xA6**c2 == xA6 # True

# yA6^C_{<E, c0, c1>}(xA6) = yA6^{<xA6><c0>}, since c0 commutes with xA6
yorb2 = [x**c0 for x in yorb]
yorbset.update({as_int(x) for x in yorb2})
len(yorbset) # 8
as_int(yA6**c2) in yorbset # False

xA6_tc = xA6**(t*c2)
xA6_tc**(xA6**(t**2)) == xA6_tc # True
xA6_tc**(yA6**(t**2)) == xA6_tc # True

"""
The additional check that $x_{A6}^{tc_2}$ commutes with $U^{t^2}$ guarantees
$c_1$ normalises $U^t$, since $\alt{6}$ has trivial centre and conjugation
by $c_2$ permutes $U, U^t, U^{t^2}$.

The same argument based on centralising elements and permuting $\alt{6}$s proves
that the element below interchanges $U$ and $U^t$ for a fourth factor of
at least 2 in $2 \times \sym{4}$. The construction of $\MT{11} \times \alt{6} \udot 2^2$ is then complete
upon applying Lemma 2.1 to $t \in \langle g_{A6}, h_{A6} \rangle$, which has
prime order 3 and takes$U^t$ to $U^{t^2} \not\subseteq U \cup U^t$.
"""

c3 = hA6**(1/t)
xA6**c3*xA6 == xA6*xA6**c3 # True
xA6**c3*yA6 == yA6*xA6**c3 # True
xA6**c3*(xA6**(t**2)) == (xA6**(t**2))*xA6**c3 # True
xA6**c3*(yA6**(t**2)) == (yA6**(t**2))*xA6**c3 # True
(xA6**t)**c3*(xA6**(t**2)) == (xA6**(t**2))*(xA6**t)**c3 # True
(xA6**t)**c3*(yA6**(t**2)) == (yA6**(t**2))*(xA6**t)**c3 # True

"""
## $\left( \alt{5} \times \unt{3}{8}{:}3 \right){:}2$ <a id="normACA"></a>
Generators are
"""

g2_ACA, g3_ACA = A5_dict["ACA"]
gACA = MM("M<y_7ach*x_407h*d_15ch*p_25808336*l_1*p_2999040*l_1*p_468643*t_2*l_2*p_2597760*l_1*p_10796555*t_2*l_2*p_1393920*l_2*p_1056432*t_2*l_1*p_2370240*t_1*l_2*p_2956800*l_1*p_127995497*t_1*l_2*p_2597760*l_1*p_96477714*t_1*l_2*p_96729600*l_2>")
hACA = MM("M<y_449h*x_35h*d_64eh*p_128178071*l_2*p_108704640*l_2*t_1*l_1*p_1499520*l_2*p_26084*l_1*t_1*l_2*p_2386560*l_2*p_465945*l_1*t_1*l_2*p_1943040*l_2*p_64122823*t_1*l_1*p_1499520*l_1*p_42729008*t_2*l_2*p_2830080*l_2*p_21543028>")
L_N = (g3_ACA, gACA, hACA)

"""
Note that $g_{3ACA}$ is one of the generators of the type ACA $\alt{5}$
in [Lemma 4.1](#lemma).   
This subgroup is the normaliser of a type ACA $\alt{5}$, in this case
also the one exhibited in [Lemma 4.1](#lemma):
"""

L_E = (g2_ACA, g3_ACA)

"""
First check that the $\alt{5}$ generators $g_{2ACA}, g_{3ACA}$ lie
in the group and let $v = g_{ACA}^4$.
"""

# g3_ACA is given as a generator
g2_ACA == gACA**3 # True
v = gACA*g2_ACA

"""
It will be shown below that $v$ centralises $\langle L_E \rangle$,
so that $g_{ACA} = v*g_{2ACA}^{-1}$ belongs to the normaliser. Check that
$h_{ACA}$ is also an element by demonstrating that it centralises $g_{2ACA}$ and
acts on $g_{3ACA}$ in such a way as to induce an outer automorphism of $\alt{5}$:
"""

hACA*g2_ACA == g2_ACA*hACA # True
A5_ACA = size_image(L_E, as_int, list)
x2_centraliser = [x for x in A5_ACA if g2_ACA*x == x*g2_ACA]

g3_ACA**hACA in A5_ACA # True
as_int(g3_ACA**hACA) in {as_int(g3_ACA**x) for x in x2_centraliser} # False

"""
To show the normaliser is generated in full, prove
$\cma{g_{2ACA}, g_{3ACA}} \cong \unt{3}{8}{:}3$
(note the $\alt{5}$ has trivial centre) is a subgroup of
$\langle h_{ACA}, v \rangle$ containing $v$. Begin
by constructing some elements thereof:
"""

b1, b2 = hACA*v, hACA*v**2
c1 = b1*b2
c2 = b1**3*b2**3
c3 = b1**3*b2

v*g2_ACA == g2_ACA*v # True
v*g3_ACA == g3_ACA*v # True
c1*g2_ACA == g2_ACA*c1 # True
c1*g3_ACA == g3_ACA*c1 # True
c2*g2_ACA == g2_ACA*c2 # True
c2*g3_ACA == g3_ACA*c2 # True
c3*g2_ACA == g2_ACA*c3 # True
c3*g3_ACA == g3_ACA*c3 # True

"""
Now compute the orders of $c_1, c_2, c_3$:
"""

c1.order() # 19
c2.order() # 7
c3.order() # 12

"""
The first two elements must lie inside the normal subgroup
$\unt{3}{8}$ of $\unt{3}{8}{:}3$,
since 7 and 19 are coprime to 3 while every non-trivial element
of the factor group 3 has order 3. The GAP Character Table Library
shows $\unt{3}{8}$ has no maximal subgroups with order divisible
by both 7 and 19, however, so that $c_1$ and $c_2$ must generate $\unt{3}{8}$.
As for the factor group $3$, observe that there are no elements of order
$\left| c_3 \right| = 12$ in $\unt{3}{8}$. It follows that $c_3$ lies in one
of the non-trivial cosets of this normal group; on the other hand, since
every non-trivial element of the cyclic group 3 generates it,
this ensures every coset is generated. The whole centraliser
of $\langle g_{2ACA}, g_{3ACA} \rangle$ thus appears.

To complete the proof, recall that $g_{2ACA}, g_{3ACA}$ lie in
$\langle g_{3ACA}, g_{ACA}, h_{ACA} \rangle$, and also that $h_{ACA}$ induces
an outer automorphism of $\langle g_{2ACA}, g_{3ACA} \rangle$. The element
$h_{ACA}$ hence lies in the part of the $\alt{5}$ normaliser outside
the $\alt{5} \times  \unt{3}{8}{:}3$, giving the entire $\left( \alt{5} \times \unt{3}{8}{:}3 \right){:}2$.
"""

"""
## $\left( \psl{3}{2} \times \symp{4}{4}{:}2 \right) \udot 2$ <a id="normL7"></a>
Generators are
"""

gL2_7 = MM("M<y_686h*x_1b55h*d_3f9h*p_29084233*l_1*p_3840*l_1*p_4176*l_1*p_10522560>")
hL2_7 = MM("M<y_144h*x_17beh*d_94eh*p_87520527*l_2*p_2830080*l_2*p_11595204*t_2*l_2*p_71005440*l_1*p_202287360*l_2*t_2*l_2*p_47942400*l_2*p_221802288*l_1*t_1*l_2*p_2344320*l_2*p_23223833*l_2*t_1*l_1*p_5639040*l_1*t_2*l_2*p_2386560*l_2*p_11142839>")
n = MM("M<y_397h*x_19d0h*d_0ccch*p_79554538*l_1*p_1499520*l_2*p_12545653>")
L_N = (gL2_7, hL2_7, n)

"""
This maximal subgroup is the normaliser of the unique conjugacy class of
$\psl{2}{3} \cong \psl{2}{7}$ in which the elements of orders 2, 3, and 7
fuse with $\MM$-classes 2A, 3A, and 7A. We claim this instance normalises
the subgroup generated by
"""

xL2_7 = gL2_7**8
yL2_7 = hL2_7**17
L_E = (xL2_7, yL2_7)

"""
As such, first show $\langle x_{L2(7)}, y_{L2(7)} \rangle \cong \psl{2}{7}$:
"""

test_xsl(xL2_7, yL2_7, 7) # True

"""
Now verify the conjugacy class fusion criteria. The subgroup is embedded in $\GG$,
allowing us to use `MM.chi_G_x0()` for this purpose.
"""

xL2_7.in_G_x0() and yL2_7.in_G_x0() # True
xL2_7.order(), yL2_7.order(), (xL2_7*yL2_7).order() # (7, 2, 3)
yL2_7.chi_G_x0()[0] #  4371
(xL2_7*yL2_7).chi_G_x0()[0] # 782
xL2_7.chi_G_x0()[0] # 50

"""
With the nature of the relevant subgroup confirmed, recall that
$x_{L2(7)}, y_{L2(7)}$ are defined as elements of $\langle g_{L2(7)}, h_{L2(7)}$.
Moreover, $u = g_{L2(7)} x_{L2(7)}^{-1}$ and $v = h_{L2(7)} y_{L2(7)}$
centralise $\langle x_{L2(7)}, y_{L2(7)} \rangle$ and thus lie in its centraliser
$\symp{4}{4}{:}2$:
"""

u = gL2_7/xL2_7
v = hL2_7*yL2_7

xL2_7*u == u*xL2_7 # True
xL2_7*v == v*xL2_7 # True
yL2_7*u == u*yL2_7 # True
yL2_7*v == v*yL2_7 # True

"""
As an immediate consequence, $g_{L2(7)} = ux_{L2(7)}$ and
$h_{L2(7)} = vy_{L2(7)}^{-1}$ belong to $\nma{x_{L2(7)}, y_{L2(7)}}$,
while $u, v \in \langle g_{L2(7)}, h_{L2(7)} \rangle$ belong
to $\cma{x_{L2(7)}, y_{L2(7)}} \cong \symp{4}{4}{:}2$.

Check also that $n \in \nma{x_{L2(7)}, y_{L2(7)}}$ by showing
it centralises $y_{L2(7)}$ and inverts $x_{L2(7)}$, thus inducing
an outer automorphism on the $\psl{2}{7}$:
"""

yL2_7**n == yL2_7 # True
xL2_7**n == 1/xL2_7 # True

"""
To confirm that $u$ and $v$ generate the centraliser,
first consider the index 2 subgroup $\symp{4}{4}$. This contains
the squares of all elements of the centraliser, and thus $z$
and the following elements of $\GG = \cm{z}$:
"""

(v*u*v)**2 == z # True
(v**2).order() # 17
# Define v_ = uv for convenience
v_ = u*v

z_cent_0 = [x**2 for x in ((v_*v*v_*u)**2*v_*u, v**3*v_*v*v_**2*v, v**2*(v*v_**2)**2*u, (v**2*v_)**2*v*u, (v_*u)**2*(v_**2*v)**2*u)]
all(x*z == z*x for x in z_cent_0) # True

"""
Data in the GAP Character Table Library reveal, however, that
the only maximal subgroup of $\symp{4}{4}$ with order
divisible by 17 is $\psl{2}{16}.2$, the centralisers of involutions
in which have orders not divisible by powers of 2 greater than 16.
That $\symp{4}{4} < \langle u, v \rangle$ will follow if it can
be shown the elements in `z_cent_0` generate a group of order 64.
"""

size_image(z_cent_0) # 64

"""
A similar argument establishes that $\langle u, v \rangle$ contains
the outer coset of $\symp{4}{4}{:}2$: involution centralisers in $symp{4}{4}$
have orders not divisible by any power of 2 greater than 256. but
"""

z_cent_1 = [(v_*v*v_*u)**2*v_, (v**2*v_)**2*v]
all(x*z == z*x for x in z_cent_1) # True
size_image(z_cent_0 + z_cent_1) # 512

"""
To complete the proof, we must prove that $n$ lies inside the normaliser but
outside this index 2 subgroup. This follows from the earlier result
that conjugation by $n$ induces an outer automorphism on the $\psl{2}{7}$:
"""

"""
## $\left( \psl{2}{11} \times \MT{12} \right){:}2$ <a id="normL11"></a>
Generators are
"""

g11 = MM("M<y_6c3h*x_1651h*d_0b2ah*p_47265823*l_1*p_1499520*l_2*p_11727906*l_2*t_2*l_2*p_1415040*l_1*p_4128*l_2*p_10295040*t_1*l_2*p_2344320*l_2*p_23192054*l_2*t_2*l_2*p_2597760*l_1*p_21929795*t_2*l_2*p_2386560*l_2*p_12578394*l_2*t_2*l_1*p_1499520*l_2*p_42673172*t_1*l_1*p_1080960>")
h11 = MM("M<y_4bdh*x_1120h*d_52ch*p_87984372*l_1*p_3840*l_1*p_21360*l_1*p_135360>")
n = MM("M<y_5feh*x_543h*d_0d13h*p_197852565*l_1*p_2640000*l_1*p_21865301*t_1*l_2*p_2830080*l_2*p_11631592*l_1*t_2*l_1*p_1499520*l_2*p_1525059*l_2*t_1*l_2*p_2344320*l_2*p_5777*t_2*l_1*p_1499520*l_1*p_10882150*t_2*l_1*p_2880*l_2*p_10667712*l_1*p_1670400*t_1*l_2*p_2814720*l_2*t_1*l_2*p_2830080*l_2*p_21463107>")
L_N = (g11, h11, n)

"""
This maximal subgroup is the normaliser of the unique conjugacy class of $\psl{2}{11}$s
in which the elements of orders 2, 3, and 5 fuse with $\MM$-classes 2A, 3A, and 5A.
We claim this instance normalises the subgroup $E$ generated
"""

g2_AAA, g3_AAA = A5_dict["AAA"]
x11 = MM("M<y_4bdh*x_120h*d_52ch*p_87984372*l_1*p_3840*l_1*p_21360*l_1*p_135360>")
L_E = (g2_AAA, x11)

"""
Note that $g_{2AAA}$ is one of the generators of the type AAA $\alt{5}$
in [Lemma 4.1](#lemma).   
As such, first show $\langle g_{2AAA}, x_{11} \rangle \cong \psl{2}{11}$:
"""

test_xsl(x11, g2_AAA, 11) # True

"""
Now verify that this our type AAA $\alt{5}$ is embedded in $E$,
ensuring the correct class fusions for elements of orders 2, 3, and 5.
"""

# g2_AAA is given as a generator of the normalised subgroup
g2_AAA*x11*g2_AAA*x11**3 == g3_AAA # True

"""
With the nature of the relevant subgroup confirmed, show that
$\langle g_{11}, h_{11} \rangle$ contains both $g_{2AAA}$ and $x_{11}$.
"""

g2_AAA == g11**3 # True
x11 == h11**12 # True

"""
Moreover, $u = g_{11} g_{2AAA}$ and $v = h_{11} x_{11}^{-1}$
(which, incidentally, equals $z \in Z \left( \GG \right)$), centralise
$\langle g_{2AAA}, x_{11} \rangle$ and thus lie in its centraliser
$\MT{12}$:
"""

u = g11*g2_AAA
v = h11/x11

x11*u == u*x11 # True
x11*v == v*x11 # True
g2_AAA*u == u*g2_AAA # True
g2_AAA*v == v*g2_AAA # True

"""
As an immediate consequence, $g_{11} = u g_{2AAA}^{-1}$ and
$h_{11} = vx_{11}$ belong to $\nma{x_{11}, g_{2AAA}}$,
while $u, v \in \langle g_{11}, h_{11} \rangle$ belong
to $\cm{E} \cong \MT{12}$.

Show that $n \in \nm{E}$ too by verifying that it centralises
$g_{2AAA}$ and inverts $x_{11}$, thus inducing
an outer automorphism of $E$:
"""

g2_AAA**n == g2_AAA # True
x11**n == 1/x11 # True

"""
Further results on the centraliser $\MT{12}$ of $E$
follow upon computation of some element orders.
"""

(v*u).order() # 11
((v*u)**4*u*v*u**2).order() # 10

"""
If $u$ and $v$ do not generate the entire $\MT{12}$, they must lie inside one of
its 3 maximal subgroups with orders divisible by 11; none of these, however,
contain elements of order 10. This shows $g_{2AAA}, x_{11}, u, v \in
    \langle g_{11}, h_{11} \rangle$ generate the index 2 subgroup
$\psl{2}{11} \times \MT{12}$ of the $\psl{2}{11}$ normaliser.

To complete the proof, we must prove that $n$ lies inside the normaliser but
outside this index 2 subgroup; it suffices to recall $n$ induced
an outer automorphism of $E$ by conjugation.
"""

"""
As an additional result, the projections $v, u$ of $h_{11}, g_{11}$ to $\MT{12}$
give standard generators thereof. Having established that they are generators,
it remains only to check that

1. $v$ belongs to conjugacy class 2B of $\MT{12}$,
2. $y$ belongs to conjugacy class 3B of $\MT{12}$, and
3. $vu$ has order 11.

According to the Online Atlas (see "Checking generators (semi-presentations)"),
however, $a, b \in \MT{12}$ of the correct orders such that
$\left( ab \right)^2 ab^2$ has order 6 belong to the required classes:
calculating the orders of four elements is thus sufficient.
"""

v.order() # 2
u.order() # 3
# The order of v*u was calculated above
((v*u)**2*v*u**2).order() # 6

"""
## $\left( \alt{7} \times \left( \alt{5} \times \alt{5} \right){:}2^2 \right){:}2$ <a id="normA7"></a>
Generators are given by
"""

gA7 = MM("M<y_1e2h*x_443h*d_576h*p_18818356*l_2*p_2597760*l_1*p_32576192*t_1*l_2*p_2956800*l_1*p_33403671*l_2*t_2*l_1*p_1920*l_2*p_465792*l_2*p_6104640*t_1*l_2*p_2830080*l_2*p_10715683*t_2*l_1*p_1499520*l_2*p_106701706*t_2*l_2*p_1943040*l_2*p_42711760*t_1*l_1*p_1457280*l_2*p_75051>")
hA7 = MM("M<y_0dch*x_772h*d_9a8h*p_64140890*l_1*p_1457280*l_2*p_11616198*t_1*l_2*p_21120*l_1*p_32504016*l_2*t_1*l_1*p_2999040*l_1*p_1948425*l_2*t_1*l_1*p_2027520*l_1*p_6740*t_1*l_2*p_2787840*l_2*p_5795*t_2*l_2*p_1457280*l_1*p_106701735*l_1*p_1900800*t_1*l_2*p_1457280*l_1*p_974609>")
L_N = (gA7, hA7)

"""
This subgroup is the normaliser of a direct product of two commuting type AAA subgroups $\alt{5}$.
We claim that this particular instance normalises $\langle U, U^{\sigma} \rangle$, where
$U = \langle L_U \rangle$ and
"""

L_U = g2_AAA, g3_AAA = A5_dict["AAA"]
σ = MM("M<y_405h*x_1e8bh*d_3efh*p_50266010*l_2*p_2956800*l_1*p_1107499*t_1*l_2*p_2386560*l_2*p_32127832*t_1*l_2*p_1457280*l_1*p_3860*t_2*l_2*p_2956800*l_1*p_11326680*t_2*l_2*p_2956800*l_1*p_12103990*l_2*t_2*l_2*p_2956800*l_1*p_63994981*t_2*l_2*p_1985280*l_1*p_85327104>")

"""
It follows from [Lemma 4.1](#lemma) that $U$, and hence also $U^{\sigma}$, are
the correct type of $\alt{5}$. Since the centre of $\alt{5}$ is trivial,
verifying that $U$ commutes with $U^{\sigma}$ will establish the required criteria
for $\langle U, U^{\sigma} \rangle$:
"""

g2_AAA*g2_AAA**σ == g2_AAA**σ*g2_AAA # True
g3_AAA*g2_AAA**σ == g2_AAA**σ*g3_AAA # True
g2_AAA*g3_AAA**σ == g3_AAA**σ*g2_AAA # True
g3_AAA*g3_AAA**σ == g3_AAA**σ*g3_AAA # True

"""
As for $\langle g_{A7}, h_{A7} \rangle$ being the normaliser of
this direct product, demonstrate that the conjugates of
$g_{2AAA}$, $g_{3AAA}$, $g_{2AAA}^{\sigma}$, and $g_{3AAA}^{\sigma}$
by $g_{A7}, h_{A7}$ fall in either $U$ or $U^{\sigma}$.
"""

# Enumerate U
U = size_image(L_U, as_int, list)
U_values = {as_int(x) for x in U}
len(U_values) # 60

# Note σ is an involution, so that x is in U^σ iff x^σ is in U
σ**2 == e # True

as_int(g2_AAA**(gA7*σ)) in U_values # True
as_int(g3_AAA**(gA7*σ)) in U_values # True
as_int((g2_AAA**σ)**gA7) in U_values # True
as_int((g3_AAA**σ)**gA7) in U_values # True
as_int(g2_AAA**hA7) in U_values # True
as_int(g3_AAA**hA7) in U_values # True
as_int((g2_AAA**σ)**(hA7*σ)) in U_values # True
as_int((g3_AAA**σ)**(hA7*σ)) in U_values # True

"""
Hence $g_{A7}, h_{A7} \in \nm{U, U^{\sigma}}$. To now prove that
they generate the normaliser of shape $\left( \alt{7} \times \left( \alt{5} \times \alt{5} \right){:}2^2 \right){:}2$, begin by exhibiting
words for $g_{2AAA}$, $g_{3AAA}$, and $\sigma$:
"""

(gA7*hA7**2*gA7*hA7)**6 == g2_AAA # True
(hA7**3*gA7**2*hA7**3)**7 == g3_AAA # True
gA7**35 == σ # True

"""
This accounts for $\langle U, U^{\sigma} \rangle$ itself (along with $\sigma$,
which will be used later). For the centralising $\alt{7}$, demonstrate
the following elements of $\langle g_{A7}, h_{A7} \rangle$ commute
with $g_{2AAA}, g_{3AAA}, \sigma$ and satisfy Carmichael's presentation
for $\alt{7}$ in Coxeter and Moser.
"""

x = (hA7*gA7*hA7*gA7**2)**6
y = (gA7*hA7**3)**4

x*g2_AAA == g2_AAA*x # True
y*g2_AAA == g2_AAA*y # True
x*g3_AAA == g3_AAA*x # True
y*g3_AAA == g3_AAA*y # True
x*σ == σ*x # True
y*σ == σ*y # True

x.order() # 5
y.order() # 3
(x*y)**7 == (y/x*y*x)**2 == (y/x**2*y*x**2)**2 == e # True

"""
Since $\alt{7}$ is simple, it indeed follows that
$\langle x, y \rangle \cong \alt{7}$.

Finally, the group $P \cong \alt{7} \times \alt{5} \times \alt{5}$
obtained thus far can  be extended to $\left( \alt{7} \times \left( \alt{5} \times \alt{5} \right){:}2^2 \right){:}2$ in three stages.
The element $a$ below induces an outer automorphism of $U$ while
centralising $U^{\sigma}$:
"""

a = (hA7*gA7**6)**15

a*(g2_AAA**σ) == (g2_AAA**σ)*a # True
a*(g3_AAA**σ) == (g3_AAA**σ)*a # True
a*g2_AAA == g2_AAA*a # True
a2_centraliser = [x for x in U if a*x == x*a]

k = as_int(g3_AAA**a)
k in U_values # True
k in {as_int(g3_AAA**x) for x in a2_centraliser} # False

"""
By Lemma 2.1, the group $\langle P, a \rangle$ is at least twice
as large $P$, no element of which induces an outer automorphism of $U$.
The same argument applies on further adding $a^{\sigma}$, which
induces an outer automorphism of $U^{\sigma}$. Appending $\sigma$
introduces a generator which does not normalise $U$ for a third
and final expansion; observing that all generators lie in
$\langle g_{A7}, h_{A7} \rangle \le \left( \alt{7} \times \left( \alt{5} \times \alt{5} \right){:}2^2 \right){:}2$, is complete.
"""

"""
## $\MT{11} \times \alt{6} \udot 2^2$ <a id="normA6"></a>
Generators are given by
"""

gM11 = MM("M<y_76dh*x_69ch*d_0fc5h*p_168600547*l_1*p_23040*l_2*p_12102096*l_1*t_1*l_2*p_2386560*l_2*p_2841156*l_2*t_1*l_1*p_960*l_2*p_10667808*l_2*p_10320000*t_1*l_1*p_1499520*l_2*p_21333334*t_2*l_2*p_2956800*l_1*p_85413698*t_1*l_2*p_2597760*l_1*p_21336226*t_1*l_1*p_1499520*l_2*p_53818915>")
hM11 = MM("M<y_4f8h*x_1df4h*d_8dfh*p_94195867*l_2*p_1985280*l_1*p_11708752*t_2*l_1*p_1457280*l_2*p_21888582*l_1*t_2*l_2*p_3840*l_2*p_464880*l_2*p_10437120*t_2*l_1*p_2640000*l_1*p_965907*t_2*l_1*p_1393920*l_1*p_10665936*l_1*p_4292160*t_1*l_2*p_2956800*l_1*p_64000715*t_1*l_1*p_1499520*l_2*p_21543068>")
L_N = (gM11, hM11)

"""
This subgroup is the normaliser of an $\MT{11}$ containing a type AAA $\alt{5}$.
We claim that it normalises the $\MT{11}$ generated by
"""

g2_AAA, g3_AAA = A5_dict["AAA"]
y4 = MM("M<y_7e8h*x_0c91h*d_0d06h*p_106445040*l_1*p_2027520*l_1*p_63998788*t_2*l_1*p_465600*l_2*p_12545568*t_1*l_2*p_1457280*l_1*p_32091441*l_2>")
L_E = (g2_AAA, y4)

"""
Note that $g_{2AAA}$ is one of the generators of the type AAA $\alt{5}$
in [Lemma 4.1](#lemma).   
First verify that $\langle g_{2AAA}, y_4 \rangle$ has the correct structure and
contains the type AAA $\alt{5}$ exhibited in [Lemma 4.1](#lemma).
"""

test_m11(g2_AAA, y4) # True
# g2_AAA is accounted for already
g2_AAA/y4*g2_AAA*y4*(g2_AAA*y4**2)**2*g2_AAA/y4*g2_AAA*y4*g2_AAA*y4**2 == g3_AAA # True

"""
This demonstrates $\langle g_{2AAA}, y_4 \rangle$ is an $\MT{11}$ of
the correct type. As for $\langle g_{M11}, h_{M11} \rangle$ being its normaliser,
derive some elements of $\cma{g_{2AAA}, y_4}$:
"""

u = gM11/y4*g2_AAA
v = hM11/((g2_AAA*y4)**3*y4)

u*g2_AAA == g2_AAA*u # True
v*g2_AAA == g2_AAA*v # True
u*y4 == y4*u # True
v*y4 == y4*v # True

"""
As an immediate consequence, $g_{M11} = u g_{2AAA}^{-1} y_4$ and
$h_{M11} = v \left( g_{2AAA} y_4 \right)^3 y_4$ belong to the normaliser
claimed, while $u, v$ belong to $\cma{g_{2AAA}, y_4} \cong \sym{6}{:}2$.

To show the normaliser is generated in full, prove $\langle g_{2AAA}, y_4 \rangle$
and its centraliser are subgroups of $\langle g_{M11}, h_{M11} \rangle$.
The first result follows upon exhibiting words in the generators
for $g_{2AAA}$ and $y_4$.
"""

gM11**30*hM11**-10 == y4 # True
gM11**-10/y4 == g2_AAA # True

"""
Since the centralising elements $u, v$ above were expressed
in terms of the elements and $g_{M11}$, $h_{M11}$,
it suffices to show that $u$ and $v$ generate the entire
$\sym{6}{:}2$. Begin by verifying that $uv^2, u$ satisfy
Moore's presentation for $\sym{6}$ given in the Online Atlas:
"""

u.order() # 2
(u*v**2).order() # 6
v.order() # 10
# Thus uv^2 u = (v^2)^u has order 10/2 = 5 as required
comm(u, u*v**2)**3 == comm(u, (u*v**2)**2)**2 == e # True
comm(u, (u*v**2)**3)**2 == comm(u, (u*v**2)**4)**2 == e # True

"""
The group $\langle u, v^2 \rangle$ is therefore either isomorphic to $\sym{6}$
or one of its factor groups 1 or 2, with the latter possibilities ruled out
by the fact that $uv^2$ has order $6$. Furthermore, the fact that
$\sym{6}$ contains no elements of order 10 ensures $\langle u, v \rangle$
is a subgroup of $\cma{g_{2AAA}, y_4} \cong \sym{6}{:}2$ at least twice as large
as $\langle u, v^2 \rangle \cong \sym{6}$, completing the proof.
"""

"""
## $\left( \sym{5} \times \sym{5} \times \sym{5} \right){:}\sym{3}$ <a id="normS5_3"></a>

Generators are given by
"""

gS5 = MM("M<y_19eh*x_0d3fh*d_9a0h*p_53285275*l_2*p_2830080*l_2*p_32553074*t_1*l_2*p_1943040*l_2*p_32471232*l_1*t_1*l_2*p_2956800*l_1*p_472405*l_2*t_1*l_1*p_2999040*l_1*p_85414663*l_2*p_960*t_2*l_2*p_2344320*l_2*p_1970481*l_2>")
hS5 = MM("M<y_13ah*x_18a5h*d_0a25h*p_220915479*l_1*p_2027520*l_1*p_23256440*l_1*t_1*l_1*p_1457280*l_2*p_22775409*l_1*t_2*l_1*p_1415040*l_2*p_465840*l_1*p_116160*t_1*l_2*p_2386560*l_2*p_21423664*t_2*l_2*p_2597760*l_1*p_43255332*t_2*l_2*p_2597760*l_1*p_96015008*t_2*l_1*p_2027520*l_1*p_5799>")
L_N = (gS5, hS5)

"""
This subgroup is the normaliser of a direct product of three commuting $\sym{5}$s containing
type AAA subgroups $\alt{5}$. We claim that this particular instance normalises
$\langle U, U^t, U^{t^2} \rangle$, where $U = \langle x_{S5}, y_{S5} \rangle$ with
"""

xS5 = MM("M<y_56fh*x_1bf7h*d_0e67h*p_181145758*l_2*p_1943040*l_2*p_23244102*t_2*l_2*p_2344320*l_2*p_21799905*l_1*t_1*l_1*p_2027520*l_1*p_12108850*l_2*t_1*l_2*p_17761920*l_2*t_1*l_2*p_960*l_1*p_3216*l_1*p_974400*t_1*l_1*p_88746240>")
yS5 = MM("M<y_4a6h*x_1d86h*d_0cbch*p_180492733*l_2*p_1900800*l_2*p_11616295>")
L_U = (xS5, yS5)

t = MM("M<y_64h*x_0f3dh*d_0fc5h*p_50814454*l_2*p_2386560*l_2*p_1946384*l_2*t_2*l_2*p_1415040*l_2*p_1904160*l_1*t_1*l_2*p_2386560*l_2*p_1510528*l_2*t_2*l_2*p_2981760*l_1*t_1*l_1*p_1499520*l_2*p_85812120*t_2*l_2*p_2956800*l_1*p_42837716*t_2*l_2*p_1943040*l_2*p_43614146*t_2*l_2*p_1943040*l_2*p_42837705>")

"""
Confirm that $U$ contains the generators $g_{2AAA}, g_{3AAA}$ of
the type AAA $\alt{5}$ provided in [Lemma 4.1](#lemma), and also that
the generators $y_{S5}, x_{S5}$ of $U$ satisfy Moore's presentation
for $\sym{5}$ given in Coxeter and Moser.
"""

g2_AAA, g3_AAA = A5_dict["AAA"]
(xS5*yS5**2)**2*xS5*yS5*xS5 == g2_AAA # True
xS5*yS5*xS5*yS5**3 == g3_AAA # True

xS5.order() # 2
yS5.order() # 5
(yS5*xS5)**4 == comm(xS5, yS5)**3 == e # True
comm(xS5, yS5**2)**2 == comm(xS5, yS5**3)**2 == e # True

"""
It follows that $U$ is a suitable $\sym{5}$ unless it is isomorphic
to a proper factor group of $\sym{5}$. The only proper factor groups,
however, are 1 and 2, neither of which can contain $y_{S5}$ of order 5.

Since $U^t$ and $U^{t^2}$ are conjugate to $U$, which has a trivial centre,
it will follows that the join of these three subgroups
(i.e. the group they generate together) is of the desired kind upon verifying
that they commute.
"""

xS5*xS5**t == xS5**t*xS5 # True
xS5*yS5**t == yS5**t*xS5 # True
yS5*xS5**t == xS5**t*yS5 # True
yS5*yS5**t == yS5**t*yS5 # True
xS5*xS5**(t**2) == xS5**(t**2)*xS5 # True
xS5*yS5**(t**2) == yS5**(t**2)*xS5 # True
yS5*xS5**(t**2) == xS5**(t**2)*yS5 # True
yS5*yS5**(t**2) == yS5**(t**2)*yS5 # True
xS5**t*xS5**(t**2) == xS5**(t**2)*xS5**t # True
xS5**t*yS5**(t**2) == yS5**(t**2)*xS5**t # True
yS5**t*xS5**(t**2) == xS5**(t**2)*yS5**t # True
yS5**t*yS5**(t**2) == yS5**(t**2)*yS5**t # True

"""
As for $\langle g_{S5}, h_{S5} \rangle$ being the $\sym{5}^3$ normaliser,
enumerate $U$ and demonstrate that the conjugates of $x_{S5}$, $y_{S5}$,
$x_{S5}^t$, $y_{S5}^t$, $x_{S5}^{t^2}$, and $y_{S5}^{t^2}$ by $g_{S5}, h_{S5}$
fall in $U^{t^i}$ for some $0 \le i \le 2$.
"""

# Note t has order 3, so that x is in U^(t^k) iff x^(t^(3-k)) is in U
t**3 == e # True
U_values = size_image((xS5, yS5), as_int, set)
len(U_values) # 120

as_int(xS5**(gS5*t)) in U_values # True
as_int(yS5**(gS5*t)) in U_values # True
as_int(xS5**(t*gS5)) in U_values # True
as_int(yS5**(t*gS5)) in U_values # True
as_int(xS5**(t**2*gS5*t**2)) in U_values # True
as_int(yS5**(t**2*gS5*t**2)) in U_values # True
as_int(xS5**hS5) in U_values # True
as_int(yS5**hS5) in U_values # True
as_int(xS5**(t*hS5*t)) in U_values # True
as_int(yS5**(t*hS5*t)) in U_values # True
as_int(xS5**(t**2*hS5*t**2)) in U_values # True
as_int(yS5**(t**2*hS5*t**2)) in U_values # True

"""
Hence $g_{S5}, h_{S5} \in \nm{U, U^t, U^{t^2}}$. To now prove that
they generate the normaliser of shape $\left( \alt{7} \times \left( \alt{5} \times \alt{5} \right){:}2^2 \right){:}2$, begin by exhibiting
words for $x_{S5}$, $y_{S5}$, and $t$:
"""

(gS5**2*hS5*gS5*hS5*gS5**2)**3 == xS5 # True
hS5**12 == yS5 # True
(gS5**4*hS5*gS5**2)**3*hS5**15 == t # True

"""
This accounts for $\langle U, U^t, U^{t^2} \rangle$ itself, along with $t$.
To complete the proof, observe that it was incidentally proved in checking
$g_{S5}, h_{S5} \in  \nm{U, U^t, U^{t^2}}$ that $h_{S5}$ normalises $U$
while interchanging $U^t$ and $U^{t^2}$. Since $t$ permutes $U, U^t, U^{t^2}$
cyclically, the action of $\langle g_{S5}, h_{S5} \rangle$ on these groups
induces the remaining $\sym{3}$.
"""

"""
## $\left( \psl{2}{11} \times \psl{2}{11} \right){:}4$ <a id="normL11_2"></a>
The following proof is adapted from Pisani and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

Our generators are
"""

g2_AAA, g3_AAA = A5_dict["AAA"]
x11 = MM("M<y_4bdh*x_120h*d_52ch*p_87984372*l_1*p_3840*l_1*p_21360*l_1*p_135360>")
x4 = MM("M<y_4a9h*x_898h*d_1ach*p_74531712*l_2*p_1900800*l_2*p_12614870*l_2*t_2*l_2*p_2344320*l_2*p_31997157*l_1*t_1*l_1*p_2880*l_2*p_21312*l_2*p_10252800*t_1*l_2*p_1900800*l_2*p_932277*t_1*l_1*p_1499520*l_2*p_64121894*t_1*l_2*p_2597760*l_1*p_42706968*t_2*l_2*p_2956800*l_1*p_42667409>")
L_N = (g2_AAA, x11, x4)

"""
Note that $g_{2AAA}$ and $x_{11}$ are is [Theorem 6.6](#normL11).  
This maximal subgroup is the normaliser of two commuting subgroups
with structure $\psl{2}{11}$ that contain AAA-type $\alt{5}$s.
It was shown above that $U = \langle g_{2AAA}, x_{11} \rangle$ is
one such $\psl{2}{11}$.
"""

L_U = (g2_AAA, x11)

"""
Check that $U$ commutes with $U^{x_4}$.
"""

g2_AAA**(g2_AAA**x4) == g2_AAA and g2_AAA**(x11**x4) == g2_AAA # True
x11**(g2_AAA**x4) == x11 and x11**(x11**x4) == x11 # True

"""
Check that $x_4$ has order $4$, and that $x_4^2$ normalises $U$;
specifically, $x_4^2$ centralises $g_{2AAA}$ and inverts $x_{11}$.
"""

x4.order() # 4
g2_AAA**(x4**2) == g2_AAA # True
x11**(x4**2) == x11**-1 # True

"""
It was noted in the proof of [Theorem 6.6](#normL11) that
this action is an outer automorphism of $U$, so
$x_4^2 \notin U \times U^{x_4}$. On the other hand, $U$ and
$U^{x_4}$ have conjugates $U^{x_4}$ and $U^{x_4^2} = U$
under $x_4$, so that $x_4 \in \nm{U \times U^{x_4}}$ and
$\langle g_{2AAA}, x_{11}, x_4 \rangle \cong \left( \psl{2}{11} \times \psl{2}{11} \right){:}4$
by an application of Lemma 2.1.
"""

"""
## $\unt{3}{4}{:}4$ <a id="unt3_4_4"></a>
The following proof is adapted from Dietrich, Lee, and Popiel.
Parts of that work, including comments, have been copied **verbatim**;
however, modifications have been made for technical and stylistic reasons,
likely introducing any errors that occur.

****

Generators are
"""

j2 = MM("M<y_538h*x_170fh*d_0a21h*p_129570785*l_1*p_1499520*l_2*p_12610123*t_2*l_1*p_2640000*l_1*p_1867433*l_1*t_2*l_2*p_1900800*l_2*p_2798997*l_2*t_2*l_1*p_1499520*l_2*p_127989729*t_2*l_2*p_2830080*l_2*p_21352704*t_2*l_2*p_1985280*l_1*p_127995457*t_1*l_2*p_2597760*l_1*p_64002648*t_1*l_2*p_1943040*l_2*p_96485380>")
a12 = MM("M<y_578h*x_309h*d_1f8h*p_113794596*l_1*p_2027520*l_1*p_10863009*t_1*l_1*p_2999040*l_1*p_1871269*l_2*t_1*l_1*p_1457280*l_2*p_12556433*l_1*t_1*l_1*p_2999040*l_1*p_6743*t_1*l_1*p_1499520*l_1*p_127990661*t_1*l_1*p_1858560*l_1*p_21408*l_2*p_240000*t_2*l_1*p_4797120*l_1*t_2*l_2*p_2830080*l_2*p_106700769>")
g2_G, g3_G = A5_dict["BCB"]
L_N = (j2, a12, g2_G)

"""
Note that $g_{3G}$ is one of the generators for the type BCB $\alt{5}$
exhibited in [Lemma 4.1](#lemma).  
Check that $j_2$ and $g_{3G}$ satisfy the presentation given
in Dietrich et al. (re-derivable via GAP) for $\unt{3}{4}$.
"""

j2**2 == g3_G**3 == (j2/g3_G*j2*g3_G)**5 == (j2*g3_G)**15 == e # True
((j2*g3_G)**3*(j2/g3_G)**3)**3 == (j2/g3_G*(j2*g3_G)**5)**4 == e # True

"""
Since $\unt{3}{4}$ is simple, this establishes that $\langle j_2, g_3 \rangle \cong \unt{3}{4}$.

To in turn show that $\langle j_2, g_{3G}, a_{12} \rangle \cong \unt{3}{4}{:}4$,
show that it contains generators $g_{2G}, g_{3G}$ for the BCB-type $\alt{5}$
given in [Lemma 4.1](#lemma). It follows from Dietrich et al. that
$N_\MM \left( \langle j_2, g_{3G} \rangle \right)$ is a maximal subgroup
of the desired structure.
"""

# g3_G is given as a generator
(j2*g3_G*j2*g3_G**2)**2*j2*g3_G**2/(g3_G*(j2*g3_G**2*j2*g3_G)**2*j2*g3_G*j2) == g2_G # True

"""
Check that $a_{12}$ has order $12$, which (noting $\unt{3}{4}$ has no elements of order 6)
does not lie in $\langle j_2, g_{3G} \rangle$.
"""

a12.order() # 12

"""
Then check that $a_{12}$ normalises $\langle j_2, g_{3G} \rangle$ by showing that it induces an automorphism thereof.
"""

((g3_G*j2)**2*g3_G**2*j2)**2/((g3_G**2*j2*(g3_G*j2)**2)**2*g3_G) == g3_G**a12 # True
(g3_G*j2*(g3_G**2*j2)**2)**2*j2/(g3_G*j2*(g3_G**2*j2)**2)**2 == j2**a12 # True

"""
This shows $\langle j_2, g_{3G}, a_12 \rangle \le \nma{j_2, g_{3G}} \cong \unt{3}{4}{:}4$.
However, neither the order of $a_{12}$ nor that of its square (12 and 6, respectively)
occur in $\unt{3}{4}$, so that this must in fact be equality.
"""
