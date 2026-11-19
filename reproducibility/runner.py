#!/usr/bin/env python3
"""Minimal launcher for prepared IoTDB installations and a single-point client."""
import argparse
import json
import math
from pathlib import Path
import re
import shlex
import subprocess
import time

ROOT = Path(__file__).resolve().parent
CLASSES = dict(raft='raft.RaftConsensus', traft='traft.TRaftConsensus',
               parallelraft='parallelraft.ParallelRaftConsensus',
               lsmraft='lsmraft.LsmRaftConsensus', iotconsensus='iot.IoTConsensus')


def command(args, dry=False, **kwargs):
    print(shlex.join(map(str, args)), flush=True)
    if not dry:
        return subprocess.run(list(map(str, args)), check=True, **kwargs)


def load(path):
    c = json.loads(path.read_text())
    if c['protocol'] not in CLASSES:
        raise ValueError('Unknown protocol')
    if not c['data_nodes']:
        raise ValueError('At least one DataNode is required')
    for node in [c['config_node']] + c['data_nodes']:
        if not re.fullmatch(r'[A-Za-z0-9_][A-Za-z0-9_.@-]*', node['ssh']):
            raise ValueError('Use a plain SSH alias or user@host')
        if not node['home'].startswith('/') or node['home'] == '/':
            raise ValueError('Use a dedicated absolute IoTDB installation directory')
    for node in c['data_nodes']:
        if not re.fullmatch(r'[A-Za-z0-9_.-]+:[0-9]+', node['endpoint']):
            raise ValueError('Endpoints must be host:port')
    for key in ['workers', 'series', 'capacity']:
        if type(c[key]) is not int or c[key] <= 0:
            raise ValueError(key + ' must be a positive integer')
    for key in ['rate_points', 'duration', 'steady_start', 'steady_end']:
        if not isinstance(c[key], (int, float)) or not math.isfinite(c[key]):
            raise ValueError(key + ' must be finite')
    if any(c[k] != int(c[k]) for k in ['duration', 'steady_start', 'steady_end']):
        raise ValueError('Measurement windows must use whole seconds')
    if not (c['rate_points'] > 0 and 0 <= c['steady_start'] < c['steady_end'] <= c['duration']):
        raise ValueError('Invalid rate or measurement window')
    return c


def remote(node, script, dry):
    return command(['ssh', '-o', 'BatchMode=yes', '--', node['ssh'],
                    'bash -lc ' + shlex.quote(script)], dry)


def preflight(c, dry):
    expected = 'org.apache.iotdb.consensus.' + CLASSES[c['protocol']]
    for node in [c['config_node']] + c['data_nodes']:
        # Parse properties without assuming key ordering or whitespace.
        script = '''import pathlib, sys
p = pathlib.Path(sys.argv[1]) / 'conf/iotdb-system.properties'
values = {}
for line in p.read_text().splitlines():
    line = line.strip()
    if line and not line.startswith(('#', '!')) and '=' in line:
        k, v = line.split('=', 1)
        values[k.strip()] = v.strip()
assert values.get('data_region_consensus_protocol_class') == sys.argv[2], 'Protocol mismatch: ' + str(p)
assert values.get('data_replication_factor') == sys.argv[3], 'Replication factor mismatch'
print('Configuration checked:', p)
'''
        remote(node, shlex.join(['python3', '-c', script, node['home'], expected,
                                  str(len(c['data_nodes']))]), dry)


def service(node, role, action, dry):
    home = shlex.quote(node['home'])
    script = f'cd {home} && bash sbin/{action}-{role}.sh'
    if action == 'start':
        script += ' -d'
    remote(node, script, dry)


def run_client(c, args):
    output = args.out.resolve()
    if output.exists():
        raise ValueError('Output directory must be new: ' + str(output))
    preflight(c, args.dry_run)
    libs = Path(c['local_iotdb_home']).expanduser().resolve() / 'lib'
    if not args.dry_run and not list(libs.glob('iotdb-session-*.jar')):
        raise ValueError('local_iotdb_home must contain lib/iotdb-session-*.jar')
    classes = ROOT / '.build'
    classpath = str(classes) + ':' + str(libs / '*')
    if not args.dry_run:
        classes.mkdir(exist_ok=True)
    command(['javac', '-encoding', 'UTF-8', '-cp', str(libs / '*'), '-d', classes,
             *sorted((ROOT / 'client').glob('*.java'))], args.dry_run)
    if args.dry_run:
        print('Would initialize a fresh database and run one single-point test at', output)
        return
    output.mkdir(parents=True)
    (output / 'config.json').write_text(json.dumps(c, indent=2) + '\n')
    # Each invocation receives a unique schema namespace; never delete existing data.
    import uuid
    database = 'root.run_' + uuid.uuid4().hex
    host, port = c['data_nodes'][0]['endpoint'].split(':')
    props = dict(factory='SessionSink', batch=1, workers=c['workers'], devices=c['series'],
                 capacity=c['capacity'], ratePoints=c['rate_points'], probability=0,
                 duration=c['duration'], steadyStart=c['steady_start'], steadyEnd=c['steady_end'],
                 seed=20261110, timestampBase=int(time.time() * 1000), drainSeconds=120,
                 output=str(output), startFile=str(output / 'start.txt'), host=host, port=port,
                 endpoints=','.join(n['endpoint'] for n in c['data_nodes']), database=database)
    def escape(value):
        return str(value).replace('\\', '\\\\').replace('\n', '\\n').replace('\r', '\\r')
    properties = output / 'driver.properties'
    properties.write_text(''.join(f'{k}={escape(v)}\n' for k, v in props.items()))
    java = ['java', '-cp', classpath]
    sql = output / 'initialize.sql'
    sql.write_text('CREATE DATABASE ' + database + '\n')
    command(java + ['ClusterSql', properties, 'execute-file', sql])
    command(java + ['ClusterSql', properties, 'initialize', str(c['series'])])
    with (output / 'client.log').open('w') as log:
        child = subprocess.Popen(java + ['OpenLoop', str(properties)], stdout=log, stderr=subprocess.STDOUT)
        try:
            deadline = time.monotonic() + 180
            while not (output / 'ready').exists():
                if child.poll() is not None or time.monotonic() > deadline:
                    raise RuntimeError('Client failed to become ready; inspect client.log')
                time.sleep(.1)
            (output / 'start.txt').write_text(str(int(time.time() * 1000) + 2000) + '\n')
            status = child.wait(timeout=c['duration'] + 300)
            if status:
                raise RuntimeError('Client failed; results retained at ' + str(output))
        finally:
            if child.poll() is None:
                child.terminate()
                try:
                    child.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    child.kill()
                    child.wait()
    print('Results:', output)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('action', choices=['start', 'stop', 'run'])
    p.add_argument('--config', type=Path, default=ROOT / 'config.json')
    p.add_argument('--dry-run', action='store_true', help='Print actions without contacting hosts or building')
    p.add_argument('--out', type=Path, default=ROOT / 'results' / time.strftime('%Y%m%d-%H%M%S'))
    args = p.parse_args()
    c = load(args.config)
    if args.action == 'start':
        preflight(c, args.dry_run)
        service(c['config_node'], 'confignode', 'start', args.dry_run)
        for node in c['data_nodes']:
            service(node, 'datanode', 'start', args.dry_run)
        print('Start commands finished. Verify SHOW CLUSTER before running the client.')
    elif args.action == 'stop':
        errors = []
        for node, role in [(n, 'datanode') for n in c['data_nodes']] + [(c['config_node'], 'confignode')]:
            try:
                service(node, role, 'stop', args.dry_run)
            except subprocess.CalledProcessError as error:
                errors.append(str(error))
        if errors:
            raise RuntimeError('\n'.join(errors))
    else:
        run_client(c, args)


if __name__ == '__main__':
    main()
