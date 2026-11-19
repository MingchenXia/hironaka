#!/usr/bin/env python3
"""Install the exact source toolchain; HTTPS+GitHub asset SHA256 required."""
import hashlib
import json
import os
from pathlib import Path
import re
import ssl
import subprocess
import sys
import tarfile
import urllib.request


class HTTPSOnlyRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, request, fp, code, msg, headers, newurl):
        if not newurl.startswith('https://'):
            raise ValueError('Non-TLS redirect rejected')
        return super().redirect_request(request, fp, code, msg, headers, newurl)


def https_open(url):
    if not url.startswith('https://'):
        raise ValueError('HTTPS required')
    ctx = ssl.create_default_context()
    ctx.minimum_version = ssl.TLSVersion.TLSv1_2
    opener = urllib.request.build_opener(urllib.request.HTTPSHandler(context=ctx), HTTPSOnlyRedirect())
    response = opener.open(urllib.request.Request(url, headers={
        'User-Agent': 'hironaka-build-cache', 'Accept': 'application/vnd.github+json'}),
        timeout=120)
    if not response.url.startswith('https://'):
        response.close()
        raise ValueError('Non-TLS redirect rejected')
    return response


def install(project, destination, opener=https_open):
    toolchain = (project / 'lean-toolchain').read_text().strip()
    match = re.fullmatch(r'leanprover/lean4:v(\d+\.\d+\.\d+(?:-rc\d+)?)', toolchain)
    if not match:
        raise ValueError('Exact official Lean release required')
    version = match[1]
    if os.uname().machine != 'x86_64':
        raise ValueError('This bundle requires the x86_64 Linux release')
    name = f'lean-{version}-linux.tar.zst'
    with opener(f'https://api.github.com/repos/leanprover/lean4/releases/tags/v{version}') as response:
        raw = response.read(2 * 1024 * 1024 + 1)
    if len(raw) > 2 * 1024 * 1024:
        raise ValueError('Release metadata exceeded bound')
    metadata = json.loads(raw)
    if metadata.get('tag_name') != 'v' + version or metadata.get('draft') is not False:
        raise ValueError('Exact published toolchain release required')
    assets = [a for a in metadata['assets'] if a['name'] == name]
    if len(assets) != 1 or not re.fullmatch(r'sha256:[0-9a-f]{64}', assets[0].get('digest', '')):
        raise ValueError('Exact unique archive with GitHub SHA256 digest required')
    asset = assets[0]
    url = f'https://github.com/leanprover/lean4/releases/download/v{version}/{name}'
    if asset['browser_download_url'] != url:
        raise ValueError('Unexpected archive origin')
    destination.mkdir(parents=True, exist_ok=False)
    archive = destination / name
    h, count = hashlib.sha256(), 0
    with opener(url) as response, archive.open('xb') as output:
        while data := response.read(1024 * 1024):
            count += len(data)
            if count > asset['size']:
                raise ValueError('Archive exceeded declared size')
            output.write(data)
            h.update(data)
    if count != asset['size'] or h.hexdigest() != asset['digest'][7:]:
        raise ValueError('Toolchain archive size/SHA256 mismatch')
    with subprocess.Popen(['zstd', '-qdc', str(archive)], stdout=subprocess.PIPE) as decode:
        with tarfile.open(fileobj=decode.stdout, mode='r|') as tar:
            for item in tar:
                root = f'lean-{version}-linux'
                if not (item.name.startswith(root+'/') or (item.name == root and item.isdir())):
                    raise ValueError('Unexpected release root')
                tar.extract(item, destination, filter='data')
        if decode.wait():
            raise RuntimeError('Toolchain decompression failed')
    prefix = destination / f'lean-{version}-linux'
    actual = subprocess.check_output([str(prefix / 'bin/lean'), '--version'], text=True).strip()
    if not re.search(r'\b' + re.escape(version) + r'\b', actual):
        raise ValueError('Installed Lean version mismatch')
    (destination / 'installation.json').write_text(json.dumps({
        'toolchain': toolchain, 'archive_sha256': h.hexdigest(), 'archive_bytes': count,
        'asset_id': asset['id'], 'lean_version': actual}, indent=2) + '\n')
    archive.unlink()  # Only the verified, locally owned compressed installer.
    if os.environ.get('GITHUB_PATH'):
        with open(os.environ['GITHUB_PATH'], 'a') as stream:
            stream.write(str(prefix / 'bin') + '\n')
    return prefix


if __name__ == '__main__':
    print(install(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()))
