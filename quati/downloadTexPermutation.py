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

  r1Name = form.getvalue('r1')
  r2Name = form.getvalue('r2')
  src_enc = form.getvalue('src')
  sig_enc = form.getvalue('sig')

  r1 = urllib.unquote(r1Name)
  r2 = urllib.unquote(r2Name)
  src = urllib.unquote(src_enc)
  sig = urllib.unquote(sig_enc)

  src_file = open("temp/spec_permutation.pl", 'w')
  sig_file = open("temp/spec_permutation.sig", 'w')

  src_file.write(src)
  sig_file.write(sig)

  src_file.close()
  sig_file.close()

  cmdStr = 'ocamlrun sellf -c permute_to_file -i temp/spec_permutation -r1 ' + r1 + ' -r2 ' + r2
  fileName = 'permutation.tex'

  # env attribute indicates where dlv.bin is located
  cmd = Popen(cmdStr, shell=True, stdout=PIPE, stderr=PIPE, env={'PATH': '/usr/local/bin:/usr/bin'})
  stdout, stderr = cmd.communicate()

  os.remove("temp/spec_permutation.pl")
  os.remove("temp/spec_permutation.sig")

  result_file = open(fileName, 'r')

  result = result_file.read()

  result_file.close()

  os.remove(fileName)

  print result

submit()
