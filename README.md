## Instructions for use

Refer to the lecture notes on Celene.

## To build the docker image (provided by students)

```bash
docker build -t verif_formelle .
```

## To start a container binding the directory to the container

```bash
docker run -it -v $(pwd):/usr/src/verification_formelle --name=conteneur_verif_formelle verif_formelle
```


