import subprocess

# solver program with parameters
SOLVER = ["z3", "-in"]

# the timeout for the solver
TIMEOUT=5


# builds the SMTLIB input for the SMT solver
def build_smt_string(cond, value):
    # TODO: HARDEN VALUE

    text = f"""
(set-info :smt-lib-version 2.6)
(set-logic QF_SLIA)
(declare-fun result () String)
{cond}
(assert (= result "{value}"))
(check-sat)
"""
    # print("text: " + text)

    return text


# checks whether a give condition is satisfied by the value
def cond_satisfied(cond, value):
    smt_str = build_smt_string(cond.smt, value)

    try:
        proc = subprocess.run(SOLVER,
                              input=smt_str,
                              capture_output=True,
                              text=True,
                              timeout=TIMEOUT,
                             )

    except Exception as error:
        print(f"error: {error}")
        return False

    if proc.returncode != 0:
        print(f"error: stdout = {proc.stdout}; stderr = {proc.stderr}")
        return False

    return "sat" in proc.stdout and "unsat" not in proc.stdout
