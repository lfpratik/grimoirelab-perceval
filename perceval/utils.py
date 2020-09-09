# -*- coding: utf-8 -*-
#
# Copyright (C) 2015-2020 Bitergia
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program. If not, see <http://www.gnu.org/licenses/>.
#
# Authors:
#     Santiago Dueñas <sduenas@bitergia.com>
#     Germán Poo-Caamaño <gpoo@gnome.org>
#     Stephan Barth <stephan.barth@gmail.com>
#     anveshc05 <anveshc10047@gmail.com>
#     Valerio Cosentino <valcos@bitergia.com>
#     Harshal Mittal <harshalmittal4@gmail.com>
#

import datetime
import email
import logging
import mailbox
import re
import sys
import os
import subprocess

import xml.etree.ElementTree

import dateutil.rrule
import dateutil.tz

import requests

from .errors import ParseError, RepositoryError


logger = logging.getLogger(__name__)


DEFAULT_DATETIME = datetime.datetime(1970, 1, 1, 0, 0, 0,
                                     tzinfo=dateutil.tz.tzutc())
DEFAULT_LAST_DATETIME = datetime.datetime(2100, 1, 1, 0, 0, 0,
                                          tzinfo=dateutil.tz.tzutc())


def check_compressed_file_type(filepath):
    """Check if filename is a compressed file supported by the tool.

    This function uses magic numbers (first four bytes) to determine
    the type of the file. Supported types are 'gz' and 'bz2'. When
    the filetype is not supported, the function returns `None`.

    :param filepath: path to the file

    :returns: 'gz' or 'bz2'; `None` if the type is not supported
    """
    def compressed_file_type(content):
        magic_dict = {
            b'\x1f\x8b\x08': 'gz',
            b'\x42\x5a\x68': 'bz2',
            b'PK\x03\x04': 'zip'
        }

        for magic, filetype in magic_dict.items():
            if content.startswith(magic):
                return filetype

        return None

    with open(filepath, mode='rb') as f:
        magic_number = f.read(4)
    return compressed_file_type(magic_number)


def months_range(from_date, to_date):
    """Generate a months range.

    Generator of months starting on `from_date` util `to_date`. Each
    returned item is a tuple of two datatime objects like in (month, month+1).
    Thus, the result will follow the sequence:
        ((fd, fd+1), (fd+1, fd+2), ..., (td-2, td-1), (td-1, td))

    :param from_date: generate dates starting on this month
    :param to_date: generate dates until this month

    :result: a generator of months range
    """
    start = datetime.datetime(from_date.year, from_date.month, 1)
    end = datetime.datetime(to_date.year, to_date.month, 1)

    month_gen = dateutil.rrule.rrule(freq=dateutil.rrule.MONTHLY,
                                     dtstart=start, until=end)
    months = [d for d in month_gen]

    pos = 0
    for x in range(1, len(months)):
        yield months[pos], months[x]
        pos = x


def message_to_dict(msg):
    """Convert an email message into a dictionary.

    This function transforms an `email.message.Message` object
    into a dictionary. Headers are stored as key:value pairs
    while the body of the message is stored inside `body` key.
    Body may have two other keys inside, 'plain', for plain body
    messages and 'html', for HTML encoded messages.

    The returned dictionary has the type `requests.structures.CaseInsensitiveDict`
    due to same headers with different case formats can appear in
    the same message.

    :param msg: email message of type `email.message.Message`

    :returns : dictionary of type `requests.structures.CaseInsensitiveDict`

    :raises ParseError: when an error occurs transforming the message
        to a dictionary
    """
    def parse_headers(msg):
        headers = {}

        for header, value in msg.items():
            hv = []

            for text, charset in email.header.decode_header(value):
                if type(text) == bytes:
                    charset = charset if charset else 'utf-8'
                    try:
                        text = text.decode(charset, errors='surrogateescape')
                    except (UnicodeError, LookupError):
                        # Try again with a 7bit encoding
                        text = text.decode('ascii', errors='surrogateescape')
                hv.append(text)

            v = ' '.join(hv)
            headers[header] = v if v else None

        return headers

    def parse_payload(msg):
        body = {}

        if not msg.is_multipart():
            payload = decode_payload(msg)
            subtype = msg.get_content_subtype()
            body[subtype] = [payload]
        else:
            # Include all the attached texts if it is multipart
            # Ignores binary parts by default
            for part in email.iterators.typed_subpart_iterator(msg):
                payload = decode_payload(part)
                subtype = part.get_content_subtype()
                body.setdefault(subtype, []).append(payload)

        return {k: '\n'.join(v) for k, v in body.items()}

    def decode_payload(msg_or_part):
        charset = msg_or_part.get_content_charset('utf-8')
        payload = msg_or_part.get_payload(decode=True)

        try:
            payload = payload.decode(charset, errors='surrogateescape')
        except (UnicodeError, LookupError):
            # Try again with a 7bit encoding
            payload = payload.decode('ascii', errors='surrogateescape')
        return payload

    # The function starts here
    message = requests.structures.CaseInsensitiveDict()

    if isinstance(msg, mailbox.mboxMessage):
        message['unixfrom'] = msg.get_from()
    else:
        message['unixfrom'] = None

    try:
        for k, v in parse_headers(msg).items():
            message[k] = v
        message['body'] = parse_payload(msg)
    except UnicodeError as e:
        raise ParseError(cause=str(e))

    return message


def remove_invalid_xml_chars(raw_xml):
    """Remove control and invalid characters from an xml stream.

    Looks for invalid characters and subtitutes them with whitespaces.
    This solution is based on these two posts: Olemis Lang's reponse
    on StackOverflow (http://stackoverflow.com/questions/1707890) and
    lawlesst's on GitHub Gist (https://gist.github.com/lawlesst/4110923),
    that is based on the previous answer.

    :param xml: XML stream

    :returns: a purged XML stream
    """
    illegal_unichrs = [(0x00, 0x08), (0x0B, 0x1F),
                       (0x7F, 0x84), (0x86, 0x9F)]

    illegal_ranges = ['%s-%s' % (chr(low), chr(high))
                      for (low, high) in illegal_unichrs
                      if low < sys.maxunicode]

    illegal_xml_re = re.compile('[%s]' % ''.join(illegal_ranges))

    purged_xml = ''

    for c in raw_xml:
        if illegal_xml_re.search(c) is not None:
            c = ' '
        purged_xml += c

    return purged_xml


def xml_to_dict(raw_xml):
    """Convert a XML stream into a dictionary.

    This function transforms a xml stream into a dictionary. The
    attributes are stored as single elements while child nodes are
    stored into lists. The text node is stored using the special
    key '__text__'.

    This code is based on Winston Ewert's solution to this problem.
    See http://codereview.stackexchange.com/questions/10400/convert-elementtree-to-dict
    for more info. The code was licensed as cc by-sa 3.0.

    :param raw_xml: XML stream

    :returns: a dict with the XML data

    :raises ParseError: raised when an error occurs parsing the given
        XML stream
    """
    def node_to_dict(node):
        d = {}
        d.update(node.items())

        text = getattr(node, 'text', None)

        if text is not None:
            d['__text__'] = text

        childs = {}
        for child in node:
            childs.setdefault(child.tag, []).append(node_to_dict(child))

        d.update(childs.items())

        return d

    purged_xml = remove_invalid_xml_chars(raw_xml)

    try:
        tree = xml.etree.ElementTree.fromstring(purged_xml)
    except xml.etree.ElementTree.ParseError as e:
        cause = "XML stream %s" % (str(e))
        raise ParseError(cause=cause)

    d = node_to_dict(tree)

    return d


class LinesCount:

    def __init__(self, git_url=None):
        self.base_path = '~/.perceval/repositories'
        self.git_url = git_url

    def __del__(self):
        pass

    @property
    def repo_path(self):
        if self.git_url:
            return self.__get_git_repo_path()

    @staticmethod
    def __get_processed_uri(uri):
        return uri.lstrip('/')

    def __get_base_path(self):
        return os.path.expanduser(self.base_path)

    def __get_git_repo_path(self):
        base_path = self.__get_base_path()
        processed_uri = self.__get_processed_uri(self.git_url)
        repo_dir = processed_uri.split('/')[-1].replace('.git', '')
        return os.path.join(base_path, repo_dir)

    @staticmethod
    def _exec(cmd, cwd=None, env=None, ignored_error_codes=None,
              encoding='utf-8'):
        """Run a command.

        Execute `cmd` command in the directory set by `cwd`. Environment
        variables can be set using the `env` dictionary. The output
        data is returned as encoded bytes.

        Commands which their returning status codes are non-zero will
        be treated as failed. Error codes considered as valid can be
        ignored giving them in the `ignored_error_codes` list.

        :returns: the output of the command as encoded bytes

        :raises RepositoryError: when an error occurs running the command
        """
        if ignored_error_codes is None:
            ignored_error_codes = []

        logger.debug("Running command %s (cwd: %s, env: %s)",
                     ' '.join(cmd), cwd, str(env))

        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE,
                                    cwd=cwd, env=env)
            (outs, errs) = proc.communicate()
        except OSError as e:
            raise RepositoryError(cause=str(e))

        if proc.returncode != 0 and proc.returncode not in ignored_error_codes:
            err = errs.decode(encoding, errors='surrogateescape')
            cause = "git command - %s" % err
            raise RepositoryError(cause=cause)
        else:
            logger.debug(errs.decode(encoding, errors='surrogateescape'))

        return outs

    def _loc(self, path):
        """
        Get the total lines of code from the default branch
        """
        total_loc = 0

        def extract_lines_of_code(value):
            status = value.decode('utf8')
            if len(status) > 0 and 'SUM:' in status:
                return int((status.split('\n')[-3]).split(' ')[-1])
            return 0

        if path and os.path.exists(path):
            cmd = ['cloc', path]
            env = {
                'LANG': 'C',
                'HOME': os.getenv('HOME', '')
            }
            result = self._exec(cmd, env=env)
            total_loc = extract_lines_of_code(result)

        return total_loc

    def _clone(self):
        pass

    def _pull(self):
        pass

    def _clean(self):
        pass

    def _fetch(self):
        pass

    def load(self):
        pass


class GitLOC(LinesCount):

    def __init__(self, url):
        super().__init__()
        self.git_url = url

    def _clone(self):
        """Clone a Git repository.

        Make a bare copy of the repository stored in `uri` into `dirpath`.
        The repository would be either local or remote.

        :param uri: URI of the repository
        :param dirtpath: directory where the repository will be cloned

        :returns: a `GitRepository` class having cloned the repository

        :raises RepositoryError: when an error occurs cloning the given
            repository
        """
        cmd = ['git', 'clone', self.git_url, self.repo_path]
        env = {
            'LANG': 'C',
            'HOME': os.getenv('HOME', '')
        }

        try:
            self._exec(cmd, env=env)
            logger.debug("Git %s repository cloned into %s",
                         self.git_url, self.repo_path)
        except (RuntimeError, Exception) as cloe:
            logger.error("Git clone error %s ", str(cloe))

    def _clean(self):
        cmd = ['rm', '-rf', self.repo_path]
        env = {
            'LANG': 'C',
            'HOME': os.getenv('HOME', '')
        }

        try:
            self._exec(cmd, env=env)
            logger.debug("Git %s repository clean", self.repo_path)
        except (RuntimeError, Exception) as cle:
            logger.error("Git clone error %s", str(cle))

    def _pull(self):

        def get_active_branch(value):
            status = value.decode('utf8')
            branch_lst = status.split('\n')
            if len(branch_lst) > 0:
                b = next((branch for branch in branch_lst
                          if branch.startswith('*')), None)
                if b:
                    return b.replace('* ', '')
                return b
            return None

        os.chdir(os.path.abspath(self.repo_path))
        env = {
            'LANG': 'C',
            'HOME': os.getenv('HOME', '')
        }
        branch = None

        try:
            cmd = ['git', 'branch', '-a']
            result = self._exec(cmd, env=env)
            branch = get_active_branch(result)
            logger.debug("Git %s repository active branch is: %s",
                         self.repo_path, branch)
        except (RuntimeError, Exception) as be:
            logger.error("Git find active branch error %s", str(be))

        try:
            if branch:
                cmd = ['git', 'pull', 'origin', branch]
                self._exec(cmd, env=env)
                logger.debug("Git %s repository pull updated code",
                             self.repo_path)
            else:
                logger.debug("Git repository active branch missing")
                logger.debug("Git %s repository pull request skip ",
                             self.repo_path)
        except (RuntimeError, Exception) as pe:
            logger.error("Git pull error %s", str(pe))

    def _fetch(self):
        os.chdir(os.path.abspath(self.repo_path))

        cmd_fetch = ['git', 'fetch']
        cmd_fetch_p = ['git', 'fetch']

        env = {
            'LANG': 'C',
            'HOME': os.getenv('HOME', '')
        }

        try:
            self._exec(cmd_fetch, env=env)
            logger.debug("Git %s fetch updated code", self.repo_path)
        except (RuntimeError, Exception) as fe:
            logger.error("Git fetch purge error %s", str(fe))

        try:
            self._exec(cmd_fetch_p, env=env)
            logger.debug("Git %s fetch purge code", self.repo_path)
        except (RuntimeError, Exception) as fpe:
            logger.error("Git fetch purge error %s", str(fpe))

    def load(self):
        if self.repo_path and not os.path.exists(self.repo_path):
            self._clone()
        else:
            self._fetch()
            self._pull()

    def fetch_loc(self):
        return self._loc(self.repo_path)
