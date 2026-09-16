# Run Chair44 (R44) yourself

[Open the notebook in Colab](https://colab.research.google.com/github/ioannist/six-birds-tiles/blob/main/notebook/r44_notebook.ipynb)
and choose **Runtime → Run all**. You can also download
[the standalone notebook](r44_notebook.ipynb) and open it in your own Jupyter environment.
Colab presents the executable cells as short named controls; use **Show code** on
any control when you want to inspect its implementation.

Rotate the existing viewer, inspect a collision box, select a parent-certificate
shell, compare the two contact sets, corrupt an input, and inspect actual periodic
controls. The final section links the global argument to quoted sources and supplied
axiom records. Download your unsigned execution receipt at the end.

This utility is not evidence for the theorem. Finite computations are T2; source
entries preserve T1/T1n/T3 and each axiom set. Display floats never decide geometry.
The notebook uses snapshot `838bca514679b2531d31f4e0dfd66641269e2a8c`, whose proof
baseline is `d90313a717`, and checks all four canonical hashes before experiments.
All output-producing checkers and mutations operate in temporary copies.

The notebook contains its own support code and evidence map: it does not fetch
unversioned implementation code from `main`. Its source fetch is restricted to the
fixed snapshot; the optional periodic controls install `python-sat==1.9.dev15`.
It never starts the long periodicity search. Interactive recognition of a reader's
own patch is deferred to U2; v1 displays and checks the parent certificates.

For Lean, use [the separate formal-build environment](LEAN.md). Reading the
committed logs inside the Python notebook is explicitly not a fresh Lean build.

The source is [r44_notebook.py](r44_notebook.py), in Jupytext percent format.
[runtime.py](runtime.py), the pin, and the generated claim map are inlined by
[build.py](build.py); `.ipynb` output cells are cleared. To reproduce locally:

```sh
python3 -m venv /tmp/r44-notebook-env
/tmp/r44-notebook-env/bin/pip install -r notebook/requirements.txt
/tmp/r44-notebook-env/bin/python notebook/build.py --check
R44_SOURCE_REPO="$PWD" /tmp/r44-notebook-env/bin/jupyter nbconvert \
  --to notebook --execute --ExecutePreprocessor.timeout=600 \
  --output=/tmp/r44-executed.ipynb notebook/r44_notebook.ipynb
```

`R44_SOURCE_REPO` supplies a local Git object database for testing; working-tree
mathematical files are not copied. Omit it to exercise the hosted network bootstrap.
The Python-only CI workflow uses the same notebook. Receipt failure/interruption
regressions are in `test_runtime.py`; `test_browser.py` independently exercises
the rendered HTML outputs with Playwright/Chromium.

Measured local execution: 98 seconds on `ai-box`, Python 3.12, 2026-09-11.
Local Chromium rendered all three frames without script errors and exercised
the periodic-cousin control, coarsening and true-scale toggle. These are local
measurements; a signed-in Colab session, its hosted runtime, and Codespaces/Docker
startup remain separate acceptance checks. No full Lean build was run for U4.
