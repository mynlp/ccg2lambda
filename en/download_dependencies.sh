#!/bin/bash

wget http://www.patrickpantel.com/download/data/verbocean/verbocean.unrefined.2004-05-20.txt.gz -P en/
python en/verbocean_to_json.py en/verbocean.unrefined.2004-05-20.txt.gz en/verbocean.json
