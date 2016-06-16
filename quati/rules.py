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

    src_enc = form.getvalue('src')
    sig_enc = form.getvalue('sig')

    src = urllib.unquote(src_enc)
    sig = urllib.unquote(sig_enc)

    if src == "":
        print "ERROR"
        print "The specification is empty."
        return
    if sig == "":
        print "ERROR"
        print "The signature is empty."
        return

    src_file = open("files/spec_rules.pl", 'w+')
    sig_file = open("files/spec_rules.sig", 'w+')

    src_file.write(src)
    sig_file.write(sig)

    src_file.close()
    sig_file.close()

    # env attribute indicates where dlv.bin is located
    cmd = Popen('ocamlrun sellf -c rules -i files/spec_rules', shell=True, stdout=PIPE, stderr=PIPE, env={'PATH': '/usr/local/bin:/usr/bin'})
    stdout, stderr = cmd.communicate()

    print stdout
    print stderr

    os.remove("files/spec_rules.pl")
    os.remove("files/spec_rules.sig")

submit()
