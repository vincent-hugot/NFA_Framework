

sudo apt install git graphviz pdftk python3-lark fonts-linuxlibertine \
  python3-pylsp idle python3-more-itertools

# LaTeX: very heavy, deactivate for faster install
#sudo apt-install texlive-extra-utils texlive-full

# get my framework, then run tests
git clone https://github.com/vincent-hugot/NFA_Framework.git
cd NFA_Framework/ || exit 1
./tests.py
xdg-open visu.pdf
