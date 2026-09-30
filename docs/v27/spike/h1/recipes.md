# H.1 recipes (reference copies, not run from the repo)

These are verbatim copies of the scripts in `~/.cache/lp-spike-h1/` that produced the H.1 results. They are kept as documentation: several start TeX engines outside `scripts/tools/_oracle.py` (the reference build, INITEX), which `check_oracle_pin.py` forbids for tracked code, so they are not committed as executable files. Each block names its source file and sha256.

## buildpdftex.sh (in ~/.cache/lp-spike-h1/)

sha256 `9b2f8b236ba3a7e54099b2337e43d103813fa3985da04d0528b08295348ec8a6`

```sh
#!/bin/sh -l
# Mirror of texlive-source@svn78081 .github/scripts/build-tl.sh, restricted to pdftex.
set -ex
arch="$1"; buildsys="$2"
case $buildsys in
  debian)
    export DEBIAN_FRONTEND=noninteractive LANG=C.UTF-8 LC_ALL=C.UTF-8
    # pin apt to the upstream build date (texlive-source svn78081 built 2026-02-23T16:24Z)
    if [ -n "$SNAP" ]; then
      rm -f /etc/apt/sources.list.d/*; printf 'deb [check-valid-until=no] http://snapshot.debian.org/archive/debian/%s bullseye main\ndeb [check-valid-until=no] http://snapshot.debian.org/archive/debian/%s bullseye-updates main\ndeb [check-valid-until=no] http://snapshot.debian.org/archive/debian-security/%s bullseye-security main\n' $SNAP $SNAP $SNAP > /etc/apt/sources.list
    fi
    apt-get update -q -y
    if [ -n "$SNAP" ]; then
      apt-get install -y --allow-downgrades libc6=2.31-13+deb11u13 libc-bin=2.31-13+deb11u13 perl-base=5.32.1-4+deb11u4
    fi
    apt-get install -y --no-install-recommends bash gcc g++ make perl libfontconfig-dev libx11-dev libxmu-dev libxaw7-dev build-essential ;;
  almalinux)
    yum update -y
    yum install -y gcc-toolset-11 fontconfig-devel libX11-devel libXmu-devel libXaw-devel perl
    . /opt/rh/gcc-toolset-11/enable ;;
esac
cd /work/repo
find . -name \*.info -exec touch '{}' \;
touch ./texk/web2c/web2c/web2c-lexer.c ./texk/web2c/web2c/web2c-parser.c ./texk/web2c/web2c/web2c-parser.h
TL_MAKE_FLAGS="-j 4"; BUILDARGS=
case "$arch" in
  aarch64-linux) BUILDARGS="--enable-arm-neon=on"; export CXXFLAGS='-std=c++17' ;;
  x86_64-linux) export CXXFLAGS='-std=c++17' ;;
esac
export TL_MAKE_FLAGS
test -n "$CFLAGS" && CFLAGS="$CFLAGS -O2"
test -n "$CXXFLAGS" && CXXFLAGS="$CXXFLAGS -O2"
export CFLAGS CXXFLAGS
gcc --version | head -1; ld --version | head -1
( rpm -q glibc gcc-toolset-11-gcc binutils 2>/dev/null || dpkg-query -W libc6 gcc-10 binutils ) || true
./Build -C --disable-all-pkgs --enable-web2c --enable-pdftex $BUILDARGS
grep -c 'compile:.* -O' Work/build.log
ls -la inst/bin/*/pdftex
sha256sum inst/bin/*/pdftex
```

## build-amd64-pdftex.sh (in ~/.cache/lp-spike-h1/)

sha256 `583e43487b743b1c492c2ce4c9cb0cbc76fcdeaa118c79d309961e93ab1ebed2`

```sh
#!/bin/sh -l
# Build ONLY the pdftex target in the configured amd64 tree (web2c's own
# Makefile), resuming after emulator crashes; then strip as TL's install-strip
# does and hash. Other engines are not needed for the pdftex binary.
yum update -y -q >/dev/null 2>&1; yum install -y -q gcc-toolset-11 fontconfig-devel libX11-devel libXmu-devel libXaw-devel perl >/dev/null 2>&1
. /opt/rh/gcc-toolset-11/enable
export CXXFLAGS='-std=c++17'
gcc --version | head -1; ld --version | head -1; strip --version | head -1
i=0; rc=1
while [ $rc -ne 0 ] && [ $i -lt 40 ]; do
  i=$((i+1)); echo "=== PDFTEX $i $(date -u)"
  (cd /work/repo/Work/texk/web2c && make -j 2 VERBOSE=1 pdftex); rc=$?
done
echo "attempts=$i final_rc=$rc"
cd /work/repo/Work/texk/web2c && ls -la pdftex && sha256sum pdftex && strip -o /tmp/pdftex.stripped pdftex && sha256sum /tmp/pdftex.stripped && ls -la /tmp/pdftex.stripped && cp /tmp/pdftex.stripped /work/pdftex.stripped-toolset
/usr/bin/strip -o /tmp/pdftex.s2 pdftex && sha256sum /tmp/pdftex.s2
exit $rc
```

## f7r.sh (in ~/.cache/lp-spike-h1/)

sha256 `e3c27a89852c1062b26d48e6fa330e82e3f533c710c2217f2ee2455e8a53b762`

```sh
set -u
cd /f7
F=$(kpsewhich -engine=pdftex pdflatex.fmt); cp $F shipped-$(uname -m).fmt
head -1 $(dirname $F)/pdflatex.log
T=$(date -u -d '2026-08-30 07:51:00' +%s); echo "epoch_start_minute $T"
for v in start plus1min; do
  E=$T; [ $v = plus1min ] && E=$((T+60))
  mkdir -p $v; (cd $v && rm -f pdflatex.* && SOURCE_DATE_EPOCH=$E FORCE_SOURCE_DATE=1 pdftex -ini -jobname=pdflatex -progname=pdflatex -translate-file=cp227.tcx '*pdflatex.ini' </dev/null >/dev/null 2>&1; echo "$v rc=$?")
  zcat $v/pdflatex.fmt > $v.raw
done
zcat shipped-$(uname -m).fmt > s.raw
sha256sum shipped-$(uname -m).fmt start/pdflatex.fmt plus1min/pdflatex.fmt
echo "raw diffs shipped vs start: $(cmp -l s.raw start.raw | wc -l)"
echo "raw diffs shipped vs plus1min:"; cmp -l s.raw plus1min.raw
echo "log diff (minus line 1):"; diff <(sed 1d $(dirname $F)/pdflatex.log) <(sed 1d start/pdflatex.log)
```

## f7amd.sh (in ~/.cache/lp-spike-h1/)

sha256 `af70f5eb536b658d96fac714ca50d1840546ba60e1b085ce72bae719c71a2e45`

```sh
set -u
cd /f7
F=$(kpsewhich -engine=pdftex pdflatex.fmt); cp $F shipped-$(uname -m).fmt
L1=$(head -1 $(dirname $F)/pdflatex.log); echo "$L1"
# the amd64 shipped build's own start minute, parsed from its log banner
D=$(echo "$L1" | sed -E 's/.*\)  ([0-9]+) ([A-Z]+) ([0-9]+) ([0-9:]+)$/\1 \2 \3 \4/')
TA=$(date -u -d "$D" +%s); echo "amd64 start minute $D epoch $TA"
TARM=$(date -u -d '2026-08-30 07:51:00' +%s)
for v in own:$TA armclock:$TARM; do
  n=${v%%:*}; E=${v#*:}
  mkdir -p $n; (cd $n && rm -f pdflatex.* && SOURCE_DATE_EPOCH=$E FORCE_SOURCE_DATE=1 pdftex -ini -jobname=pdflatex -progname=pdflatex -translate-file=cp227.tcx '*pdflatex.ini' </dev/null >/dev/null 2>&1; echo "$n rc=$?")
done
sha256sum shipped-$(uname -m).fmt own/pdflatex.fmt armclock/pdflatex.fmt
```

## fmar1/fmasrc.sh (in ~/.cache/lp-spike-h1/)

sha256 `bedbef25334331451b798415ed84116e2b5b19101f8121a605b882189b4a967a`

```sh
set -u
apt-get update -qq >/dev/null 2>&1; apt-get install -y -qq binutils >/dev/null 2>&1
B=/w/b-arm64/repo/Work/texk/web2c/pdftex
objdump -d -l --no-show-raw-insn $B > /w/fmar1/dis.txt
python3 - <<'PY' 2>/dev/null || awk -f /dev/null
PY
echo done
```

## harness/h1cmp.py (in ~/.cache/lp-spike-h1/)

sha256 `4e5ac1cb8923d01681520421eac752b129364cb4b8573cd2d7cd1115d571577d`

```python
#!/usr/bin/env python3
"""H.1 reproduction harness (scratch, NOT committed: it starts an engine outside
_oracle.py for the REFERENCE build only).

For each document: the PINNED binary runs through _oracle.py (get_oracle(),
run_pdflatex = graded env, allow-listed argv) following run_to_fixpoint's pass
protocol exactly; the REFERENCE binary runs the same protocol in a container of
the SAME pinned image with the reference bin dir mounted at
/usr/local/texlive/2026/bin/ref (a sibling of bin/<arch>, so kpathsea's
SELFAUTOPARENT, texmf.cnf and pdflatex.fmt are the image's), with the SAME
environment (engine_env(graded_env(tex_env(td)))), argv and pass logic.
Every pass's outputs are saved; comparison is done by h1diff.py.

usage: h1cmp.py SET ARCH ENGINES WORKERS [--trace]
  SET: strict | real | real20 | strict20 ; ARCH: arm64|amd64 ; ENGINES: pinned,ref
"""
import hashlib, json, os, shutil, subprocess, sys, tempfile, threading, time, uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

REPO = Path("/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/.claude/worktrees/spike-h1")
sys.path.insert(0, str(REPO / "scripts/tools"))
SP = Path(__file__).resolve().parent
W = Path.home() / ".cache/lp-spike-h1"
CORPUS = Path("/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Archives/"
              "LP_v24_FULL_BACKUP_20250716_165548/corpus/papers")
TIMEOUT = int(os.environ.get("LP_H1_TIMEOUT", "300"))
MAX_PASSES = 3

SET, ARCH, ENGINES, WORKERS = sys.argv[1], sys.argv[2], sys.argv[3].split(","), int(sys.argv[4])
TRACE = "--trace" in sys.argv
# --fixclock: the cross-architecture arm. Both architectures run with
# FORCE_SOURCE_DATE=1 and one fixed SOURCE_DATE_EPOCH, added AFTER the
# protocol's variables by wrapping graded_env (the #625 clock-experiment
# precedent); everything else is the oracle's own code path. This removes the
# real clock (\time, \day, \month, \year, \today) as a confound between runs made
# hours apart; it does not fix \pdfrandomseed (seeded from the real time).
FIXCLOCK = "--fixclock" in sys.argv
FIXED_EPOCH = "1788076260"  # 2026-08-30 07:51 UTC
PLAT = {"arm64": "linux/arm64", "amd64": "linux/amd64"}[ARCH]
os.environ["LP_ORACLE_WORKROOT"] = os.environ.get(
    "LP_H1_WORKROOT", str(Path.home() / ".cache/lp-oracle" / f"work-h1-{ARCH}"))
if ARCH == "amd64":
    os.environ["DOCKER_DEFAULT_PLATFORM"] = PLAT
import _oracle as O  # noqa: E402
if FIXCLOCK:
    _orig_graded_env = O.graded_env

    def _graded_env_fixclock(env):
        out = _orig_graded_env(env)
        out["FORCE_SOURCE_DATE"] = "1"
        out["SOURCE_DATE_EPOCH"] = FIXED_EPOCH
        return out
    O.graded_env = _graded_env_fixclock

OUT = W / "runs" / (SET + ("-trace" if TRACE else "") + ("-fixclock" if FIXCLOCK else "")
                    + os.environ.get("LP_H1_TAG", "")) / ARCH
OUT.mkdir(parents=True, exist_ok=True)


def docs():
    if SET in ("strict", "strict20", "strict8"):
        d = json.load(open(REPO / "corpora/strict_s0/bytes_probes.json"))
        out = []
        for key in ("documents", "outside"):
            for r in d[key]:
                if r.get("hex"):
                    b = bytes.fromhex(r["hex"])
                else:  # >HEX_MAX files, regenerated from _strict_bytes and matched by sha256
                    b = (W / "nohex" / r["sha256"]).read_bytes()
                assert hashlib.sha256(b).hexdigest() == r["sha256"], (key, r["i"])
                out.append({"id": f"bp-{key[0]}{r['i']:05d}", "hex": b.hex(),
                            "toplevel": "doc.tex", "family": r["family"]})
        if SET == "strict8":  # the cross-architecture sample: every 8th document, in file order
            out = out[::8]
        if SET == "strict20":
            ids = set(json.load(open(SP / "strict20_ids.json")))
            out = [r for r in out if r["id"] in ids]
            assert len(out) == len(ids)
        return out
    w = json.load(open(SP / "window_2000_2199.json"))
    rows = [{"id": r["arxiv_id"], "toplevel": r["toplevel"]} for r in w]
    if SET in ("real20", "real7", "real13"):  # real13: the 13 amd64 grades made before the mutation guard existed (review round 1)
        ids = set(json.load(open(SP / f"{SET}_ids.json")))
        rows = [r for r in rows if r["id"] in ids]
        assert len(rows) == len(ids)
    return rows


def materialise(doc, work: Path, top_holder: list):
    if "hex" in doc:
        work.mkdir()
        (work / "doc.tex").write_bytes(bytes.fromhex(doc["hex"]))
    else:
        shutil.copytree(CORPUS / doc["id"], work)
    top = doc["toplevel"]
    if TRACE:
        wrapper = "h1trace.tex"
        (work / wrapper).write_bytes(b"\\tracingall\\tracingonline=0 \\input{" + top.encode() + b"}\n")
        top = wrapper
    top_holder.append(top)


REF_NAME = f"lp-h1-ref-{ARCH}" + ("-" + Path(os.environ["LP_H1_WORKROOT"]).name
                                  if os.environ.get("LP_H1_WORKROOT") else "")
_ref_lock = threading.Lock()


def ensure_ref(workroot: Path):
    with _ref_lock:
        p = subprocess.run(["docker", "inspect", "--format", "{{.State.Running}}", REF_NAME],
                           capture_output=True)
        if p.returncode == 0 and p.stdout.strip() == b"true":
            return
        subprocess.run(["docker", "rm", "-f", REF_NAME], capture_output=True)
        refbin = W / f"refbin-{ARCH}"
        assert (refbin / "pdftex").is_file() and (refbin / "pdflatex").is_symlink(), refbin
        subprocess.run(["docker", "run", "-d", "--platform", PLAT, "--name", REF_NAME,
                        "-v", f"{workroot}:{workroot}",
                        "-v", f"{refbin}:/usr/local/texlive/2026/bin/ref:ro",
                        "-e", "HOME=/tmp", "--entrypoint", "sleep", O.IMAGE, "infinity"],
                       check=True, capture_output=True)
        time.sleep(1)


REF_PATH = "/usr/local/texlive/2026/bin/ref:" + O.IMAGE_ENV["PATH"]


def ref_exec(cwd: Path, args, env, timeout):
    """Mirror of ContainerOracle._exec for the reference binary."""
    tex = O.engine_env(O.graded_env(env), {})
    cmd = ["docker", "exec", "-w", str(cwd), "-e", "HOME=/tmp", "-e", f"PATH={REF_PATH}"]
    for k, v in sorted(tex.items()):
        cmd += ["-e", f"{k}={v}"]
    nonce = "LP_H1_RC_" + uuid.uuid4().hex
    script = ('n=$1; t=$2; e=$3; shift 3; timeout -k 10 "$t" "$e" "$@"; '
              'rc=$?; printf "\\n%s=%d\\n" "$n" "$rc" >&2')
    cmd += [REF_NAME, "sh", "-c", script, "sh", nonce, str(timeout), "pdflatex", *args]
    p = subprocess.run(cmd, capture_output=True, timeout=timeout + 90)
    import re
    m = re.search(rb"^" + nonce.encode() + rb"=(\d+)$", p.stderr, re.M)
    if m is None:
        raise RuntimeError("ref exec: no rc line: " + p.stderr.decode(errors="replace")[:300])
    rc = int(m.group(1))
    err = p.stderr[:m.start()] + p.stderr[m.end():]
    if b"This is pdfTeX" not in p.stdout:
        raise RuntimeError(f"ref exec: no banner rc={rc}: " + (p.stdout + err)[:300].decode(errors="replace"))
    return rc, p.stdout + err, rc in (124, 137)


def snapshot(work: Path, src_hashes: dict, dest: Path, rc, to, out: bytes):
    dest.mkdir(parents=True, exist_ok=True)
    files = {}
    for f in sorted(work.rglob("*")):
        if not f.is_file():
            continue
        rel = str(f.relative_to(work))
        h = hashlib.sha256(f.read_bytes()).hexdigest()
        if src_hashes.get(rel) == h:
            continue
        files[rel] = h
        tgt = dest / rel.replace("/", "__")
        shutil.copyfile(f, tgt)
    (dest / "__stdout").write_bytes(out)
    return {"rc": rc, "timed_out": to, "files": files}


def protocol(run, work: Path, top: str, env, src_hashes, dest: Path):
    passes = []
    halt = True
    args = ["-interaction=nonstopmode"] + (["-halt-on-error"] if halt else []) + [top]
    rc = -1
    for k in range(MAX_PASSES):
        rc, out, to = run(work, args, env, TIMEOUT)
        passes.append(snapshot(work, src_hashes, dest / f"p{k + 1}", rc, to, out))
        if to or rc == 0:
            break
    if TRACE:
        return passes  # traced comparisons: step behaviour of the passes run, no confirming pass
    if passes[-1]["timed_out"] or rc != 0:
        return passes
    rc, out, to = run(work, args, env, TIMEOUT)
    passes.append(snapshot(work, src_hashes, dest / f"p{len(passes) + 1}", rc, to, out))
    return passes


# CONTAINER-MUTATION GUARD. Under qemu-user emulation (amd64 on this arm64
# host) a crashed mktex helper made mktexmf write a generated .mf into the
# image's texmf-dist and mktexupd rewrite texmf-dist/ls-R (MEASURED 2026-09-30,
# 22:49:47 UTC, container of work-h1-amd64). A grade made in a mutated
# container is not a grade of the image. So every container this harness uses
# is checked after every document: the size and mtime of every ls-R of the
# installation, and no file of /usr/local/texlive newer than the container.
# On a change the document is recorded as mutated.json (never result.json) and
# the run stops taking documents.
LSR = ("/usr/local/texlive/2026/texmf-dist/ls-R /usr/local/texlive/2026/texmf-var/ls-R "
       "/usr/local/texlive/2026/texmf-config/ls-R")
STOP = threading.Event()


def container_state(name):
    p = subprocess.run(["docker", "exec", name, "sh", "-c",
                        f"stat -c '%n %s %Y' {LSR}; "
                        "find /usr/local/texlive -xdev -type f -newer /etc/hostname | head -5"],
                       capture_output=True, timeout=600)
    return p.stdout.decode(errors="replace")


BASE = {}


def containers(oracle):
    names = [oracle.name]
    if "ref" in ENGINES:
        names.append(REF_NAME)
    return names


def one(doc, oracle):
    res = {"id": doc["id"]}
    rdir = OUT / doc["id"]
    if (rdir / "result.json").is_file():
        return json.load(open(rdir / "result.json"))
    if STOP.is_set():
        return {"id": doc["id"], "skipped": "stopped after a container mutation"}
    for eng in ENGINES:
        td = Path(oracle.mkdtemp(prefix="h1-"))
        try:
            work = td / "w"
            holder = []
            materialise(doc, work, holder)
            top = holder[0]
            src = {str(f.relative_to(work)): hashlib.sha256(f.read_bytes()).hexdigest()
                   for f in work.rglob("*") if f.is_file()}
            env = oracle.tex_env(td)
            t0 = time.time()
            if eng == "pinned":
                runner = lambda c, a, e, t: oracle.run_pdflatex(c, a, e, t)  # noqa: E731
            else:
                ensure_ref(oracle.workroot)
                runner = ref_exec
            passes = protocol(runner, work, top, env, src, rdir / eng)
            res[eng] = {"passes": passes, "td": str(td), "secs": round(time.time() - t0, 2)}
        except Exception as e:  # recorded, never silently a result
            res[eng] = {"error": repr(e)[:500]}
        finally:
            try:
                oracle.remove([p for p in td.rglob("*") if p.is_file()])
            except Exception:
                pass
            shutil.rmtree(td, ignore_errors=True)
    rdir.mkdir(parents=True, exist_ok=True)
    changed = {}
    for n in containers(oracle):
        if n in BASE:
            now = container_state(n)
            if now != BASE[n]:
                changed[n] = now
    if changed:
        STOP.set()
        res["container_mutated"] = changed
        json.dump(res, open(rdir / "mutated.json", "w"), indent=1)
        return res
    json.dump(res, open(rdir / "result.json", "w"), indent=1)
    return res


def main():
    oracle = O.get_oracle()
    prov = oracle.provenance()
    json.dump(prov, open(OUT / "oracle_provenance.json", "w"), indent=1)
    print("oracle:", prov, flush=True)
    if "ref" in ENGINES:
        ensure_ref(oracle.workroot)
    for n in containers(oracle):
        BASE[n] = container_state(n)
        if len(BASE[n].strip().splitlines()) != 3:
            raise SystemExit(f"container {n} already holds files newer than itself: {BASE[n]}")
    print("container baseline:", BASE, flush=True)
    ds = docs()
    print(f"{len(ds)} documents, engines {ENGINES}, arch {ARCH}", flush=True)
    done = [0]
    lock = threading.Lock()

    def job(d):
        r = one(d, oracle)
        with lock:
            done[0] += 1
            if done[0] % 25 == 0:
                print(f"{done[0]}/{len(ds)} {time.strftime('%H:%M:%S')}", flush=True)
        return r
    with ThreadPoolExecutor(WORKERS) as ex:
        list(ex.map(job, ds))
    errs = [p for p in OUT.glob("*/result.json")
            if any("error" in v for k, v in json.load(open(p)).items() if isinstance(v, dict))]
    mut = list(OUT.glob("*/mutated.json"))
    print(f"done; {len(errs)} with errors; {len(mut)} mutated; stopped={STOP.is_set()}", flush=True)


if __name__ == "__main__":
    main()
```

## archsem/probes/run.sh (in ~/.cache/lp-spike-h1/, review round 2)

sha256 `bbce7ca0b479de3b141e1f6cfa669c8b1c36c09b4949bbed207263619381114d`

```sh
cd /w
for t in *.tex; do f=${t%.tex}
  H=-halt-on-error; case $f in nh-*) H=;; esac; rm -rf o-$f; mkdir o-$f; cp $t *.jpg *.pdf o-$f/ 2>/dev/null
  (cd o-$f && SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 timeout 300 pdftex $H -interaction=nonstopmode $t </dev/null > term.txt 2>&1; echo "$f rc=$?")
  grep -ohE '^!.*|\[[a-zA-Z0-9=-]+=[^]]*\]|too (large|small)[^.]*|number too big|invalid[^.]*' o-$f/term.txt | tr '\n' ' ' | cut -c1-500 | sed 's/^/   /'; echo
  [ -f o-$f/$f.pdf ] && grep -aoE '/Rect \[[^]]*\]' o-$f/$f.pdf | tr '\n' ' ' | sed 's/^/   /'; echo
done
```

## archsem/probes/run2.sh (in ~/.cache/lp-spike-h1/, review round 2)

sha256 `8f374495aaab30d70a80606b023abcd1a6ee0b1dd265a50b8eeca5246cd82b3d`

```sh
cd /w
for t in slant*.tex; do f=${t%.tex}
  rm -rf o-$f; mkdir o-$f; cp $t o-$f/
  (cd o-$f && SOURCE_DATE_EPOCH=1788076260 FORCE_SOURCE_DATE=1 timeout 300 pdftex -halt-on-error -interaction=nonstopmode $t </dev/null > term.txt 2>&1; echo "$f rc=$?")
  grep -ohiE 'warning[^)]*|^!.*' o-$f/$f.log | tr '\n' ' ' | cut -c1-300 | sed 's/^/   /'; echo
  [ -f o-$f/$f.pdf ] && sha256sum o-$f/$f.pdf | cut -c1-16 | sed 's/^/   pdf sha256 /'
done
```

## archsem/dis.sh (in ~/.cache/lp-spike-h1/, review round 2)

sha256 `dc78cffe2622c8f9d2a4289076a92b12a28f5c1fbd4f26ad36d3a4a34d0d3884`

```sh
set -e
objdump -d -l --no-show-raw-insn /w/b-arm64/repo/Work/texk/web2c/pdftex > /o/arm64.dis
objdump -d -l --no-show-raw-insn /w/b-amd64/repo/Work/texk/web2c/pdftex > /o/amd64.dis
objdump -d --no-show-raw-insn -M intel /w/b-amd64/repo/Work/texk/web2c/pdftex > /o/amd64.intel.dis
echo done
```

## archsem/dis_sc.sh (in ~/.cache/lp-spike-h1/, review round 2)

sha256 `7256d858b9b8ac3f63d52e3b87c4b1ea4811348f3f7ee10bf049e300c1048253`

```sh
objdump -d --no-show-raw-insn /w/b-arm64-sc/repo/Work/texk/web2c/pdftex > /o/arm64-sc.dis
objdump -d --no-show-raw-insn /w/b-arm64/repo/Work/texk/web2c/pdftex > /o/arm64-base.dis
```

## archsem/dis_wv.sh (in ~/.cache/lp-spike-h1/, review round 2)

sha256 `288b967e066a80067cc8a6dac06cbac91ad21771ce3370b2184d78ff6a621496`

```sh
objdump -d --no-show-raw-insn /w/b-arm64-wrapv/repo/Work/texk/web2c/pdftex > /o/arm64-wrapv.dis
```

## archsem/Dockerfile (in ~/.cache/lp-spike-h1/, review round 2)

sha256 `c712d2828cfbf74b5109709e1d471b1f33e15cb7348a269861b4bf6d5db6524c`

```sh
FROM arm64v8/debian:bullseye
RUN apt-get update -qq && apt-get install -y -qq binutils-multiarch binutils >/dev/null && rm -rf /var/lib/apt/lists/*
```

## the probe invocation (review round 2)

```sh
for a in arm64 amd64; do docker run --rm --platform linux/$a -v $PWD/r-$a:/w texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b sh -c 'uname -m; sh /w/run.sh' > r-$a.out 2>&1; done
# run2.sh likewise for the slant*.tex documents (t-$a.out); the variant builds:
docker run --rm --platform linux/arm64 -e SNAP=20260223T160000Z -v $W/b-arm64-sc:/work -v $W/archsem/buildpdftex-signedchar.sh:/b.sh:ro arm64v8/debian:bullseye sh -l /b.sh aarch64-linux debian
```
