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

    src_file = open("files/spec.pl", 'w')
    sig_file = open("files/spec.sig", 'w')

    src_file.write(src)
    sig_file.write(sig)

    src_file.close()
    sig_file.close()

    #input = open("coherence.in", "r")
    cmd = Popen('./sellf.bin -i files/spec -c initialcoherence', shell=True, stdout=PIPE, stderr=PIPE)
    stdout, stderr = cmd.communicate()

    print stdout
    print stderr

    os.remove("files/spec.pl")
    os.remove("files/spec.sig")

submit()
