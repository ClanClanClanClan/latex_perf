#!/bin/zsh
# cmp.sh RUN PREFIX: meancompare.py of a model run against the binary's run of the same prefix
r=$1 p=$2; H5=~/.cache/lp-spike-h1/h5; W=${0:a:h}/../../../../..
cp $H5/runs/$r/stdout $H5/runs/$r/dump/driver.out
python3 $W/docs/v27/spike/h3/tools/meancompare.py --repo $W --names $H5/in/$p/names.json --spec $H5/in/$p/spec \
  --model $H5/runs/$r/dump --bin $H5/runs/bincmp-$p --out $H5/runs/$r/compare.json > /dev/null
python3 -c "import json,sys; d=json.load(open(sys.argv[1])); print({k: d[k] for k in d if not isinstance(d[k], (dict, list))})" $H5/runs/$r/compare.json
