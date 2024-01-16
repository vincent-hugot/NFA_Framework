#!/bin/bash

dnf install git graphviz pdftk python3-pyls-spyder idle linux-libertine-fonts-common
pip install lark

#TODO LaTeX packages?

git clone https://github.com/vincent-hugot/NFA_Framework.git
cd NFA_Framework || exit 1
./tests.py
xdg-open visu.pdf
