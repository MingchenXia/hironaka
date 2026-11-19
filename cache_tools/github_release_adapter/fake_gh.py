#!/usr/bin/env python3
"""TEST EXECUTABLE: local JSON state only. Has no networking implementation."""
import base64
import json
import os
from pathlib import Path
import sys
from urllib.parse import urlsplit, parse_qs, unquote

p = Path(os.environ['MOCK_GH_STATE'])
s = json.loads(p.read_text())
a = sys.argv[1:]
s.setdefault('calls', []).append(a)

def save():
    p.write_text(json.dumps(s))

def fail():
    save()
    sys.stderr.write('mock operation failed\n')
    sys.exit(3)

def metadata(x):
    return {k: v for k, v in x.items() if k != 'data'}

def output(x):
    save()
    print(json.dumps(x))

if a and a[0] == 'api':
    assert a[1:3] == ['--hostname', 'github.com']
    endpoint = next(v for v in a if v.startswith(('/repos/', 'https://uploads.github.com/')))
    u = urlsplit(endpoint)
    route = u.path
    if '--method' in a and a[a.index('--method')+1] == 'POST':
        assert endpoint.startswith('https://uploads.github.com/')
        assert route == '/repos/o/r/releases/7/assets'
        assert 'Content-Type: application/octet-stream' in a
        name = parse_qs(u.query)['name'][0]
        f = Path(a[a.index('--input')+1]); assert f.name == name
        if any(x['name'] == name for x in s['assets']): fail()
        data = f.read_bytes()
        x = {'id': s['next_id'], 'name': name, 'state': 'uploaded', 'size': len(data),
             'data': base64.b64encode(data).decode()}
        s['next_id'] += 1; s['assets'].append(x)
        if s.pop('upload_after_error', False): fail()
        output(metadata(x))
    elif '/releases/tags/' in route:
        assert unquote(route.split('/releases/tags/')[1]) == s['release']['tag_name']
        output(s['release'])
    elif route == '/repos/o/r/releases/7/assets':
        page = int(parse_qs(u.query)['page'][0])
        output([metadata(x) for x in s['assets'][(page-1)*100:page*100]])
    elif route.startswith('/repos/o/r/releases/assets/'):
        ident = int(route.rsplit('/', 1)[1])
        x = next((x for x in s['assets'] if x['id'] == ident), None)
        if x is None: fail()
        if '--method' in a:
            assert a[a.index('--method')+1] == 'PATCH'
            assert a[a.index('--input')+1] == '-'
            data = json.load(sys.stdin); assert data == {'name': 'cache.json'}
            if any(y['name'] == 'cache.json' and y['id'] != ident for y in s['assets']): fail()
            x['name'] = data['name']
            if s.pop('rename_after_error', False): fail()
            output(metadata(x))
        else:
            assert 'Accept: application/octet-stream' in a
            save(); sys.stdout.buffer.write(base64.b64decode(x['data']))
    else:
        raise AssertionError('Unexpected API route')
else:
    raise AssertionError('Unexpected mock command; create/delete/publish prohibited')
