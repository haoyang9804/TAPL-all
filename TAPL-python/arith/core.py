from syntax import *

class NoRuleApplies(Exception):
  pass

def is_numeric_val(t: Term) -> bool:
  return isinstance(t, TmZero) or \
    isinstance(t, TmSucc) and is_numeric_val(t._value)
    
def eval_1_step(t: Term) -> Term:
  if isinstance(t, TmIf):
    if isinstance(t._condition, TmTrue):
      return eval_1_step(t._true_branch)
    elif isinstance(t._condition, TmFalse):
      return eval_1_step(t._false_branch)
    else:
      return TmIf(eval_1_step(t._condition), t._true_branch,\
        t._false_branch, info=t.info)
  elif isinstance(t, TmSucc):
    return TmSucc(eval_1_step(t._value), info=t.info)
  elif isinstance(t, TmPred):
    if isinstance(t._value, TmZero):
      return TmZero()
    elif isinstance(t._value, TmSucc) and is_numeric_val(t._value._value):
      return t._value._value
    else:
      return TmPred(eval_1_step(t._value), info=t.info)
  elif isinstance(t, TmIsZero):
    if isinstance(t._value, TmZero):
      return TmTrue()
    elif isinstance(t._value, TmSucc):
      return TmFalse()
    else:
      return TmIsZero(eval_1_step(t._value))
  else:
    raise NoRuleApplies()
      
def eval(t: Term) -> Term:
  try:
    return eval(eval_1_step(t))
  except NoRuleApplies:
    return t

if __name__ == "__main__":

  def test_numeric():
    assert is_numeric_val(TmZero())
    assert is_numeric_val(TmSucc(TmZero()))
    assert is_numeric_val(TmSucc(TmSucc(TmZero())))

    assert not is_numeric_val(TmTrue())
    assert not is_numeric_val(TmSucc(TmTrue()))
    assert not is_numeric_val(TmSucc(TmSucc(TmTrue())))


  def test_eval():
    for t in TmTrue(), TmFalse(), TmZero(), TmSucc(TmZero()):
        assert eval(t) is t
    
    print(repr(
      eval(
      TmIf(
        TmTrue(),
        TmIf(
          TmFalse(),
          TmZero(),
          TmSucc(TmSucc(TmPred(TmSucc(TmZero()))))
        ),
        TmFalse()
      ))
    ))
    
    print(repr(
      TmSucc(TmSucc(TmZero()))
    ))
  
  test_numeric()
  test_eval()