## To build the docker image

```bash
docker build -t verif_formelle .
```

## To start a container binding the directory to the container

```bash
docker run -it -v .:/usr/scr/verif_formelle --name=conteneur_verif_formelle verification_formelle
```


