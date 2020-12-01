# Use the official image as a parent image.
FROM python:3.9-buster


# Set the working directory.
WORKDIR /usr/src/verification_formelle

# Run the command inside your image filesystem.
RUN apt-get update && apt-get install -y \
  graphviz \
  pdftk

CMD [ "/bin/bash" ]