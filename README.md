agda-nbe
========

# Content

This repository explores type-directed partial evaluation of
various lambda-calculi equipped with rich reduction relations.
The development axis involve: baking soundness directly in the
model definition, separating normalization and standardization
or performing only weak-head normalization.

The repository is organized in this way:

* __tools/__

  Generic tools to formalize calculi and their reduction
  rules. Currently contains a formalization of transitive
  reflexive (symmetric) closures and (non dependent) contexts.

* __stlc/__

  Simply typed lambda calculus: always a good start when trying
  out new ideas.

* __stlcl/__

  Simply typed lambda calculus with lists, products and a
  unit type and a reduction relation having special rules
  to deal with map, fold, append and their fusion.

* __stlci/__

  Simply typed lambda calculus with a universe of finitely
  branching inductive skeleton and their eliminators /
  recursors.


# Development versions

This repository will host only (quite) stable formalizations.
The ongoing developments happen at patch-tag:

http://patch-tag.com/r/gallais/agda

# License

All the .agda files in the repository agda-nbe are licensed under
GPLv3.

agda-nbe is a formalization of nbe for different lambda calculi
Copyright (C) 2012 allais guillaume <guillaume.allais@ens-lyon.org>

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
