## Instructions for use

INSA students: refer to the lecture notes on Celene.


## Installation

Linux: Use the appropriate script in NFA_install_scripts.

Windows: c.f. lecture notes


## To build the docker image (provided by students)

```bash
docker build -t verif_formelle .
```

## To start a container binding the directory to the container

```bash
docker run -it -v $(pwd):/usr/src/verification_formelle --name=conteneur_verif_formelle verif_formelle
```


