# the contract generator's meanings_sha256, recomputed from one log of a meaning dump
import sys, json, hashlib
sys.path.insert(0, sys.argv[1] + '/scripts/tools')
import gen_contract as g
names = json.load(open(sys.argv[2]))
d = g.parse_dump(open(sys.argv[3], 'rb').read())
m = {g.name_str(g.name_bytes(n)): d['meanings'].get(i) for i, n in enumerate(names)}
und = [n for n, v in m.items() if v is None]
defined = {n: g.name_str(v) for n, v in m.items() if v is not None}
dig = hashlib.sha256("\n".join("%s\t%s" % (n, defined[n]) for n in sorted(defined)).encode("utf-8")).hexdigest()
k = json.load(open(sys.argv[1] + '/corpora/contracts/kernel/aarch64-a476533c0d6e64f0.json'))
print(json.dumps({"records": len(d['meanings']), "defined": len(defined), "undefined": len(und), "error": d['error'],
                  "digest": dig, "contract_digest": k['meanings_sha256'], "equal": dig == k['meanings_sha256']}))
