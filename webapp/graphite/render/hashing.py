"""Copyright 2008 Orbitz WorldWide
   Copyright 2011 Chris Davis

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License."""

from hashlib import md5
from itertools import chain
import bisect
import sys

#try:
#    from builtins import int
#except ImportError:
#    import __builtin__ as builtins
#    from builtins import int

try:
    import mmh3
except ImportError:
    mmh3 = None

try:
    import pyhash

    def fnv1a(data, seed=2166136261, mode=32, seed64=14695981039346656037):
        hasher = pyhash.fnv1a_32()
        if mode > 32:
            hasher = pyhash.fnv1a_64()
            seed=seed64
        return hasher(data, seed=seed)

except ImportError:
    def fnv1a(data, seed=2166136261, mode=32, seed64=14695981039346656037):
        """
        FNV-1a Hash (http://isthe.com/chongo/tech/comp/fnv/) in Python.
        Taken from https://gist.github.com/vaiorabbit/5670985
        """
        hval = seed
        fnv_prime = 16777619
        uint_max = 2 ** 32
        if mode > 32:
            fnv_prime = 1099511628211
            uint_max = 2 ** 64
            hval = seed64
        for s in data:
            try:
                hval = hval ^ s
            except TypeError:
                hval = hval ^ ord(s)
            hval = (hval * fnv_prime) % uint_max
        return hval


def fnv32a(data, seed=2166136261):
    return fnv1a(data, seed, mode=32)


try:
    import jump

    def jump_hash(key, num_buckets):
        return jump.hash(int(key), num_buckets)
except ImportError:
    def jump_hash(key, num_buckets):
        """Fast, minimal memory, consistent hash algorithm.
        Taken from https://github.com/lithammer/python-jump-consistent-hash/blob/master/src/jump/__init__.py
        C version is 10 times faster, use jump-consistent-hash module if possible
        Accepts only integer as input
        """
        b, j = -1, 0
        if num_buckets < 1:
            raise ValueError(
                "'num_buckets' must be a positive number, got %d" % num_buckets
            )
        while j < num_buckets:
            b = int(j)
            key = ((int(key) * int(2862933555777941757)) + 1) & 0xFFFFFFFFFFFFFFFF
            j = float(b + 1) * (float(1 << 31) / float((key >> 33) + 1))
        return int(b)


def xorshift64(x):
    """
    XorShift generates a predictable random-ish hash from the given integer.
    This method is also used by carbon-c-relay for replication in a Jump hash ring.
    https://en.wikipedia.org/wiki/Xorshift
    http://vigna.di.unimi.it/ftp/papers/xorshift.pdf
    https://github.com/grobian/carbon-c-relay/blob/v3.6/consistent-hash.c#L363-L368
    https://rosettacode.org/wiki/Pseudo-random_numbers/Xorshift_star#Python
    """
    x = (x ^ (x >> 12)) & 0xFFFFFFFFFFFFFFFF
    x = (x ^ (x << 25)) & 0xFFFFFFFFFFFFFFFF
    x = (x ^ (x >> 27)) & 0xFFFFFFFFFFFFFFFF
    return (x * 0x2545F4914F6CDD1D) & 0xFFFFFFFFFFFFFFFF


def hashRequest(request):
    # Normalize the request parameters to ensure we're deterministic
    queryParams = [
        "%s=%s" % (key, '&'.join(values))
        for (key,values) in chain(request.POST.lists(), request.GET.lists())
        if not key.startswith('_')
    ]
    normalizedParams = ','.join( sorted(queryParams) )
    return compactHash(normalizedParams)


def hashData(targets, startTime, endTime, xFilesFactor):
    targetsString = ','.join(sorted(targets))
    startTimeString = startTime.strftime("%Y%m%d_%H%M")
    endTimeString = endTime.strftime("%Y%m%d_%H%M")
    myHash = targetsString + '@' + startTimeString + ':' + endTimeString + ':' + str(xFilesFactor)
    return compactHash(myHash)


def compactHash(string):
    return md5(string.encode('utf-8')).hexdigest()


def carbonHash(key, hash_type, modulo=1):
    if hash_type == 'fnv1a_ch':
        big_hash = int(fnv1a(key.encode('utf-8')))
        small_hash = (big_hash >> 16) ^ (big_hash & 0xffff)
    elif hash_type == 'jump_fnv1a_ch':
        big_hash = int(fnv1a(key.encode('utf-8'), mode=64))
        small_hash = jump_hash(big_hash, modulo)
    elif hash_type == 'mmh3_ch':
        if mmh3 is None:
            raise Exception('Install "mmh3" to use this hashing function.')
        small_hash = mmh3.hash(key)
    else:
        big_hash = compactHash(key)
        small_hash = int(big_hash[:4], 16)
    return small_hash


class ConsistentHashRing:
    def __init__(self, nodes, replica_count=100, hash_type='carbon_ch'):
        self.ring = []
        self.ring_len = len(self.ring)
        self.nodes = set()
        self.nodes_len = len(self.nodes)
        self.replica_count = replica_count
        self.hash_type = hash_type
        for node in nodes:
            self.add_node(node)

    def compute_ring_position(self, key):
        return carbonHash(key, self.hash_type)

    def add_node(self, key):
        self.nodes.add(key)
        self.nodes_len = len(self.nodes)
        for i in range(self.replica_count):
            if self.hash_type == 'fnv1a_ch':
                replica_key = "%d-%s" % (i, key[1])
            else:
                replica_key = "%s:%d" % (key, i)
            position = self.compute_ring_position(replica_key)
            while position in [r[0] for r in self.ring]:
                position = position + 1
            entry = (position, key)
            bisect.insort(self.ring, entry)
        self.ring_len = len(self.ring)

    def remove_node(self, key):
        self.nodes.discard(key)
        self.nodes_len = len(self.nodes)
        self.ring = [entry for entry in self.ring if entry[1] != key]
        self.ring_len = len(self.ring)

    def get_node(self, key):
        assert self.ring
        position = self.compute_ring_position(key)
        search_entry = (position, ())
        index = bisect.bisect_left(self.ring, search_entry) % self.ring_len
        entry = self.ring[index]
        return entry[1]

    def get_nodes(self, key):
        nodes = set()
        if not self.ring:
            return
        if self.nodes_len == 1:
            for node in self.nodes:
                yield node
        position = self.compute_ring_position(key)
        search_entry = (position, ())
        index = bisect.bisect_left(self.ring, search_entry) % self.ring_len
        last_index = (index - 1) % self.ring_len
        nodes_len = len(nodes)
        while nodes_len < self.nodes_len and index != last_index:
            next_entry = self.ring[index]
            (position, next_node) = next_entry
            if next_node not in nodes:
                nodes.add(next_node)
                nodes_len += 1
                yield next_node

            index = (index + 1) % self.ring_len


class JumpConsistentHashRing(ConsistentHashRing, object):
    def __init__(self, nodes, replica_count=1, hash_type='jump_fnv1a_ch'):
        super(JumpConsistentHashRing, self).__init__(nodes, replica_count, hash_type)

    def compute_ring_position(self, key):
        return carbonHash(key, self.hash_type, modulo=len(self.ring))

    def add_node(self, key):
        # https://github.com/grobian/carbon-c-relay/blob/v3.6/consistent-hash.c#L293
        # https://github.com/jjneely/buckytools/blob/master/hashing/jump.go#L96
        (server, instance) = key  # (server, instance) = node
        if instance == 'None' or instance == '':
            self.ring.append(key)
        else:
            bisect.insort(self.ring, key)
        self.ring_len = len(self.ring)

    # used only in tests?
    def get_node(self, key):
        assert self.ring
        position = self.compute_ring_position(key)
        return self.ring[position]

    # this used in carbonlink.py and carbon too
    def get_nodes(self, key):
        nodes = set()
        if not self.ring:
            return
        if self.nodes_len == 1:
            for node in self.nodes:
                yield node
        # https://github.com/grobian/carbon-c-relay/blob/v3.6/consistent-hash.c#L340
        # https://github.com/jjneely/buckytools/blob/master/hashing/jump.go#L130
        hash = fnv1a(key.encode('utf-8'), mode=64)  # jump hash accepts only integers
        ring = self.ring
        index = self.ring_len
        replica_count = self.replica_count
        while index > 0:
            position = jump_hash(hash, index)
            nodes.add(self.ring[position])
            yield self.ring[position]
            replica_count = replica_count - 1
            if replica_count <= 0:
                return
            # use xorshift to generate a different hash for input in the jump hash again
            hash = xorshift64(hash)
            # remove the server we just selected, such that we can
            # be sure the next iteration will fetch another server
            index = index - 1
            ring[position] = ring[index]
        return
