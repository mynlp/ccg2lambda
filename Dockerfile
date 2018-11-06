FROM python:3.6.3-jessie

ENV LC_ALL=C.UTF-8
ENV LANG=C.UTF-8

MAINTAINER Masashi Yoshikawa <yoshikawa.masashi.yh8@is.naist.jp>

# Install Java
RUN echo "deb http://http.debian.net/debian jessie-backports main" >>/etc/apt/sources.list
RUN apt-get update
RUN apt-get install -y -t jessie-backports openjdk-8-jdk

# Install ccg2lambda specific dependencies
RUN apt-get update --fix-missing && \
    apt-get install -y \
        ant \
        bc \
        coq=8.4pl4dfsg-1 \
        libxml2-dev \
        libxslt1-dev && \
    rm -rf /var/lib/apt/lists/*

RUN pip install lxml simplejson pyyaml -I nltk==3.0.5 cython chainer==4.0.0
RUN python -c "import nltk; nltk.download('wordnet')"

WORKDIR /app
ADD . /app

# Install C&C
WORKDIR /app/parsers
ADD http://www.cl.cam.ac.uk/~sc609/resources/candc-downloads/candc-linux-1.00.tgz /app/parsers/candc-linux-1.00.tgz
RUN tar xvf candc-linux-1.00.tgz
WORKDIR /app/parsers/candc-1.00
ADD http://www.cl.cam.ac.uk/~sc609/resources/candc-downloads/models-1.02.tgz /app/parsers/candc-1.00/models-1.02.tgz
RUN tar xvf models-1.02.tgz && \
    echo "/app/parsers/candc-1.00" >> /app/en/candc_location.txt && \
    echo "candc:/app/parsers/candc-1.00" >> /app/en/parser_location.txt

# Install easyccg
WORKDIR /app/parsers
RUN git clone https://github.com/mikelewis0/easyccg
WORKDIR /app/parsers/easyccg
ADD https://drive.google.com/uc?export=download&id=0B7AY6PGZ8lc-dUN4SDcxWkczM2M /app/parsers/easyccg/model.tar.gz
RUN tar xvf model.tar.gz && echo "easyccg:"`pwd` >> /app/en/parser_location.txt

# Install EasySRL
RUN git clone https://github.com/uwnlp/EasySRL /app/parsers/EasySRL
WORKDIR /app/parsers/EasySRL
# Download model file (the ugly script is due to downloading the large file from Google Drive)
RUN wget --load-cookies /tmp/cookies.txt "https://docs.google.com/uc?export=download&confirm=$(wget --quiet \
    --save-cookies /tmp/cookies.txt --keep-session-cookies --no-check-certificate \
    'https://docs.google.com/uc?export=download&id=0B7AY6PGZ8lc-R1E3aTA5WG54bWM' -O- | \
    sed -rn 's/.*confirm=([0-9A-Za-z_]+).*/\1\n/p')&id=0B7AY6PGZ8lc-R1E3aTA5WG54bWM" -O model.tar.gz 2> /dev/null && \
    rm -rf /tmp/cookies.txt
RUN ant && tar xvf model.tar.gz && \
    echo "easysrl:/app/parsers/EasySRL/" >> /app/en/parser_location.txt

# Install Jigg
WORKDIR /app/parsers
ADD https://github.com/mynlp/jigg/archive/v-0.4.tar.gz /app/parsers/v-0.4.tar.gz
RUN tar xzf v-0.4.tar.gz
ADD https://github.com/mynlp/jigg/releases/download/v-0.4/ccg-models-0.4.jar /app/parsers/jigg-v-0.4/jar/
RUN echo "/app/parsers/jigg-v-0.4" > /app/ja/jigg_location.txt && \
    echo "jigg:/app/parsers/jigg-v-0.4" >> /app/ja/parser_location_ja.txt

# Install depccg
WORKDIR /app/parsers
RUN git clone https://github.com/masashi-y/depccg
WORKDIR /app/parsers/depccg/models
ADD http://cl.naist.jp/~masashi-y/resources/depccg/en_hf_tri.tar.gz  /app/parsers/depccg/models/en_hf_tri.tar.gz
ADD http://cl.naist.jp/~masashi-y/resources/depccg/ja_hf_ccgbank.tar.gz /app/parsers/depccg/models/ja_hf_ccgbank.tar.gz
RUN tar xvf en_hf_tri.tar.gz && tar xvf ja_hf_ccgbank.tar.gz
WORKDIR /app/parsers/depccg/src
RUN python setup.py build_ext --inplace 2> /dev/null && \
    echo "depccg:/app/parsers/depccg/" >> /app/en/parser_location.txt && \
    echo "depccg:/app/parsers/depccg/" >> /app/ja/parser_location_ja.txt

WORKDIR /app
RUN cp ./en/coqlib_sick.v ./coqlib.v && coqc coqlib.v
RUN cp ./en/tactics_coq_sick.txt ./tactics_coq.txt
# CMD ["en/rte_en_mp_any.sh", "en/sample_en.txt", "en/semantic_templates_en_emnlp2015.yaml"]
CMD ["/bin/bash"]
