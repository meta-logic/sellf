#!/usr/bin/python

import cgi
import cgitb
import os
import urllib
from subprocess import Popen, PIPE

#show error messages on browser
cgitb.enable()

def submit():

    print "Content-type: text/html\n"

    form = cgi.FieldStorage()
 
    systemName = form.getvalue('system')
    r1Number = form.getValue('r1')
    r2Number = form.getValue('r2')

    system = urllib.unquote(systemName)
    r1 = urllib.unquote(r1Number)
    r2 = urllib.unquote(r2Number)

    if system == "":
        print "ERROR"
        print "No system specified."
        return

    cmd = Popen('./sellf -c permutation -i examples/' + system + ' -r1 ' + r1 + ' -r2 ' + r2, shell=True, stdout=PIPE, stderr=PIPE)
    stdout, stderr = cmd.communicate()

    print stdout
    print stderr

submit()
