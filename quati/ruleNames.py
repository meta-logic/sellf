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

    system = urllib.unquote(systemName)

    if system == "":
        print "ERROR"
        print "No system specified."
        return

    cmd = Popen('./sellf -c rulenames -i examples/' + system, shell=True, stdout=PIPE, stderr=PIPE)
    stdout, stderr = cmd.communicate()

    print stdout
    print stderr

submit()
