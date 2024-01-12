
# update/upgrade system, then install packages
sudo pacman -Syu
sudo pacman -S --needed git pdftk graphviz python tk xz python-pip mpdecimal \
  python-lsp-server python-lark-parser libertinus-font

# LaTeX: very heavy, deactivate for faster install
#sudo pacman -S --needed texlive-binextra texlive-core

# get my framework, then run tests
git clone https://github.com/vincent-hugot/NFA_Framework.git
cd NFA_Framework/ || return
./tests.py
xdg-open visu.pdf
