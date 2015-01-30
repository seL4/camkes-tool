#!/usr/bin/env python

'''
Run pylint on a Jinja 2 template.
'''

import jinja2, os, subprocess, sys, tempfile

# Clagged pieces from the runner.
START_BLOCK = '/*-'
END_BLOCK = '-*/'
START_VARIABLE = '/*?'
END_VARIABLE = '?*/'
START_COMMENT = '/*#'
END_COMMENT = '#*/'

def main(argv, out, err):
    if len(argv) < 2 or argv[1] in ['--help', '-?']:
        print >>err, 'usage: %s file pylint_args...' % argv[0]
        return -1

    if not os.path.exists(argv[1]):
        print >>err, '%s not found' % argv[1]
        return -1

    root, template = os.path.split(os.path.abspath(argv[1]))

    # Construct a Jinja environment that matches that of the runner.
    env = jinja2.Environment(
        loader=jinja2.FileSystemLoader(root),
        extensions=["jinja2.ext.do", "jinja2.ext.loopcontrols"],
        block_start_string=START_BLOCK,
        block_end_string=END_BLOCK,
        variable_start_string=START_VARIABLE,
        variable_end_string=END_VARIABLE,
        comment_start_string=START_COMMENT,
        comment_end_string=END_COMMENT)

    # Compile the template requested to a temporary directory.
    tmp = tempfile.mkdtemp()
    print >>out, 'compiling to %s...' % tmp
    env.compile_templates(tmp, filter_func=lambda x: x == template, zip=None,
        ignore_errors=False)

    # Find it and run pylint on it.
    py = os.path.join(tmp, os.listdir(tmp)[0])
    print 'running pylint on %s...' % py
    return subprocess.call(['pylint', py] + argv[2:])

if __name__ == '__main__':
    sys.exit(main(sys.argv, sys.stdout, sys.stderr))
