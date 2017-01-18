import os
import re
import subprocess
import xml.etree.ElementTree as ET
import signal

from collections import deque, namedtuple

Ok = namedtuple('Ok', ['val', 'msg'])
Err = namedtuple('Err', ['err'])

Inl = namedtuple('Inl', ['val'])
Inr = namedtuple('Inr', ['val'])

StateId = namedtuple('StateId', ['id'])
Option = namedtuple('Option', ['val'])

OptionState = namedtuple('OptionState', ['sync', 'depr', 'name', 'value'])
OptionValue = namedtuple('OptionValue', ['val'])

Status = namedtuple('Status', ['path', 'proofname', 'allproofs', 'proofnum'])

Goals = namedtuple('Goals', ['fg', 'bg', 'shelved', 'given_up'])
Goal = namedtuple('Goal', ['id', 'hyp', 'ccl'])
Evar = namedtuple('Evar', ['info'])

def parse_response(xml):
    assert xml.tag == 'value'
    if xml.get('val') == 'good':
        return Ok(parse_value(xml[0]), None)
    elif xml.get('val') == 'fail':
        print('err: %s' % ET.tostring(xml))
        return Err(parse_error(xml))
    else:
        assert False, 'expected "good" or "fail" in <value>'

def parse_value(xml):
    if xml.tag == 'unit':
        return ()
    elif xml.tag == 'bool':
        if xml.get('val') == 'true':
            return True
        elif xml.get('val') == 'false':
            return False
        else:
            assert False, 'expected "true" or "false" in <bool>'
    elif xml.tag == 'string':
        return xml.text or ''
    elif xml.tag == 'int':
        return int(xml.text)
    elif xml.tag == 'state_id':
        return StateId(int(xml.get('val')))
    elif xml.tag == 'list':
        return [parse_value(c) for c in xml]
    elif xml.tag == 'option':
        if xml.get('val') == 'none':
            return Option(None)
        elif xml.get('val') == 'some':
            return Option(parse_value(xml[0]))
        else:
            assert False, 'expected "none" or "some" in <option>'
    elif xml.tag == 'pair':
        return tuple(parse_value(c) for c in xml)
    elif xml.tag == 'union':
        if xml.get('val') == 'in_l':
            return Inl(parse_value(xml[0]))
        elif xml.get('val') == 'in_r':
            return Inr(parse_value(xml[0]))
        else:
            assert False, 'expected "in_l" or "in_r" in <union>'
    elif xml.tag == 'option_state':
        sync, depr, name, value = map(parse_value, xml)
        return OptionState(sync, depr, name, value)
    elif xml.tag == 'option_value':
        return OptionValue(parse_value(xml[0]))
    elif xml.tag == 'status':
        path, proofname, allproofs, proofnum = map(parse_value, xml)
        return Status(path, proofname, allproofs, proofnum)
    elif xml.tag == 'goals':
        return Goals(*map(parse_value, xml))
    elif xml.tag == 'goal':
        return Goal(*map(parse_value, xml))
    elif xml.tag == 'evar':
        return Evar(*map(parse_value, xml))
    elif xml.tag == 'xml' or xml.tag == 'richpp':
        return ''.join(xml.itertext())

def parse_error(xml):
    return ET.fromstring(re.sub(r"<state_id val=\"\d+\" />", '', ET.tostring(xml)))

def build(tag, val=None, children=()):
    attribs = {'val': val} if val is not None else {}
    xml = ET.Element(tag, attribs)
    xml.extend(children)
    return xml

def encode_call(name, arg):
    return build('call', name, [encode_value(arg)])

def encode_value(v):
    if v == ():
        return build('unit')
    elif isinstance(v, bool):
        xml = build('bool', str(v).lower())
        xml.text = str(v)
        return xml
    elif isinstance(v, str):
        xml = build('string')
        xml.text = v
        return xml
    elif isinstance(v, int):
        xml = build('int')
        xml.text = str(v)
        return xml
    elif isinstance(v, StateId):
        return build('state_id', str(v.id))
    elif isinstance(v, list):
        return build('list', None, [encode_value(c) for c in v])
    elif isinstance(v, Option):
        xml = build('option')
        if v.val is not None:
            xml.set('val', 'some')
            xml.append(encode_value(v.val))
        else:
            xml.set('val', 'none')
        return xml
    elif isinstance(v, Inl):
        return build('union', 'in_l', [encode_value(v.val)])
    elif isinstance(v, Inr):
        return build('union', 'in_r', [encode_value(v.val)])
    # NB: `tuple` check must be at the end because it overlaps with () and
    # namedtuples.
    elif isinstance(v, tuple):
        return build('pair', None, [encode_value(c) for c in v])
    else:
        assert False, 'unrecognized type in encode_value: %r' % (type(v),)

coqtop = None
states = []
state_id = None
root_state = None

def kill_coqtop():
    global coqtop
    if coqtop:
        try:
            coqtop.terminate()
            coqtop.communicate()
        except OSError:
            pass
        coqtop = None

def ignore_sigint():
    signal.signal(signal.SIGINT, signal.SIG_IGN)

def escape(cmd):
    return cmd.replace("&nbsp;", ' ') \
              .replace("&apos;", '\'') \
              .replace("&#40;", '(') \
              .replace("&#41;", ')')

def get_answer():
    fd = coqtop.stdout.fileno()
    messageNode = None
    while True:
        try:
            data = os.read(fd, 0x4000)
            try:
                elt = ET.fromstring('<coqtoproot>' + escape(data) + '</coqtoproot>')
                shouldWait = True
                valueNode = None
                for c in elt:
                    if c.tag == 'value':
                        shouldWait = False
                        valueNode = c
                    if c.tag == 'message':
                        messageNode = c[1]
                if shouldWait:
                    continue
                else:
                    vp = parse_response(valueNode)
                    if messageNode is not None:
                        if isinstance(vp, Ok):
                            return Ok(vp.val, parse_value(messageNode))
                    return vp
            except ET.ParseError:
                continue
        except OSError:
            # coqtop died
            return None

def call(name, arg, encoding='utf-8'):
    xml = encode_call(name, arg)
    msg = ET.tostring(xml, encoding)
    send_cmd(msg)
    response = get_answer()
    return response

def send_cmd(cmd):
    coqtop.stdin.write(cmd)

def restart_coq(*args):
    global coqtop, root_state, state_id
    if coqtop: kill_coqtop()
    options = [ 'coqtop'
              , '-ideslave'
              , '-main-channel'
              , 'stdfds'
              , '-async-proofs'
              , 'on'
              ]
    try:
        if os.name == 'nt':
            coqtop = subprocess.Popen(
                options + list(args)
              , stdin = subprocess.PIPE
              , stdout = subprocess.PIPE
              , stderr = subprocess.STDOUT
            )
        else:
            coqtop = subprocess.Popen(
                options + list(args)
              , stdin = subprocess.PIPE
              , stdout = subprocess.PIPE
              , preexec_fn = ignore_sigint
            )

        r = call('Init', Option(None))
        assert isinstance(r, Ok)
        root_state = r.val
        state_id = r.val
    except OSError:
        print("Error: couldn't launch coqtop")

def launch_coq(*args):
    restart_coq(*args)

def cur_state():
    if len(states) == 0:
        return root_state
    else:
        return state_id

def advance(cmd, encoding = 'utf-8'):
    global state_id
    r = call('Add', ((cmd, -1), (cur_state(), True)), encoding)
    if r is None:
        return r
    if isinstance(r, Err):
        return r
    states.append(state_id)
    state_id = r.val[0]
    return r

def rewind(step = 1):
    global states, state_id
    assert step <= len(states)
    idx = len(states) - step
    state_id = states[idx]
    states = states[0:idx]
    return call('Edit_at', state_id)

def query(cmd, encoding = 'utf-8'):
    r = call('Query', (cmd, cur_state()), encoding)
    return r

def goals():
    return call('Goal', ())

def read_states():
    return states
