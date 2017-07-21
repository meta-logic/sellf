#!/usr/bin/python

import cgi
import cgitb
import os

# show error messages on browser
cgitb.enable()

def load():

  print "Content-type: text/html\n"
  
  form = cgi.FieldStorage()
  
  if form.getvalue('example'):
    name = form.getvalue('example')
  else:
    print "% No example selected.##EOF##% No example selected."
    return

  src_file = open("../examples/proofsystems/"+name+".pl", 'r')
  sig_file = open("../examples/proofsystems/"+name+".sig", 'r')

  src = src_file.read()
  sig = sig_file.read()

  src_file.close()
  sig_file.close()

  print src+"##EOF##"+sig

load()
