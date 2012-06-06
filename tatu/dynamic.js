// Because of Firefox's incompatibility with innerText
function setText(node, text) {
  if(node.innerText !== undefined) {
    node.innerText = text;
  }
  else {
    node.textContent = text;
  }
}

function cutcoherence() {  
  var xmlhttp = false;
  if (window.XMLHttpRequest) {
    // code for IE7+, Firefox, Chrome, Opera, Safari
    xmlhttp=new XMLHttpRequest();
  }
  else {
  // code for IE6, IE5
    xmlhttp=new ActiveXObject("Microsoft.XMLHTTP");
  }

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      //document.getElementById("result_text").innerText = xmlhttp.responseText;
      setText(document.getElementById("result_text"), xmlhttp.responseText);
    }
  }
 
  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value
  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)
  var params = "src="+src_enc+"&sig="+sig_enc

  xmlhttp.open("POST", "cutcoherence.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  //xmlhttp.setRequestHeader("Content-length", params.length);
  //xmlhttp.setRequestHeader("Connection", "close");
  xmlhttp.send(params)
}

function initcoherence() {  
  var xmlhttp = false;
  if (window.XMLHttpRequest) {
    // code for IE7+, Firefox, Chrome, Opera, Safari
    xmlhttp=new XMLHttpRequest();
  }
  else {
  // code for IE6, IE5
    xmlhttp=new ActiveXObject("Microsoft.XMLHTTP");
  }

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      //document.getElementById("result_text").innerText = xmlhttp.responseText;
      setText(document.getElementById("result_text"), xmlhttp.responseText);
    }
  }
 
  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value
  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)
  var params = "src="+src_enc+"&sig="+sig_enc

  xmlhttp.open("POST", "initialcoherence.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  //xmlhttp.setRequestHeader("Content-length", params.length);
  //xmlhttp.setRequestHeader("Connection", "close");
  xmlhttp.send(params)
}

function principalcut() {  
  var xmlhttp = false;
  if (window.XMLHttpRequest) {
    // code for IE7+, Firefox, Chrome, Opera, Safari
    xmlhttp=new XMLHttpRequest();
  }
  else {
  // code for IE6, IE5
    xmlhttp=new ActiveXObject("Microsoft.XMLHTTP");
  }

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      //document.getElementById("result_text").innerText = xmlhttp.responseText;
      setText(document.getElementById("result_text"), xmlhttp.responseText);
    }
  }
 
  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value
  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)
  var params = "src="+src_enc+"&sig="+sig_enc

  xmlhttp.open("POST", "principalcut.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  //xmlhttp.setRequestHeader("Content-length", params.length);
  //xmlhttp.setRequestHeader("Connection", "close");
  xmlhttp.send(params)
}

function atomicelim() {  
  var xmlhttp = false;
  if (window.XMLHttpRequest) {
    // code for IE7+, Firefox, Chrome, Opera, Safari
    xmlhttp=new XMLHttpRequest();
  }
  else {
  // code for IE6, IE5
    xmlhttp=new ActiveXObject("Microsoft.XMLHTTP");
  }

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      //document.getElementById("result_text").innerText = xmlhttp.responseText;
      setText(document.getElementById("result_text"), xmlhttp.responseText);
    }
  }
 
  var src = document.getElementById("specification").value
  var sig = document.getElementById("signature").value
  var src_enc = encodeURIComponent(src)
  var sig_enc = encodeURIComponent(sig)
  var params = "src="+src_enc+"&sig="+sig_enc

  xmlhttp.open("POST", "atomicelim.py", true)
  xmlhttp.setRequestHeader("Content-type", "application/x-www-form-urlencoded");
  //xmlhttp.setRequestHeader("Content-length", params.length);
  //xmlhttp.setRequestHeader("Connection", "close");
  xmlhttp.send(params)
}

function getExample() {
  var xmlhttp = false;
  if (window.XMLHttpRequest) {
    // code for IE7+, Firefox, Chrome, Opera, Safari
    xmlhttp=new XMLHttpRequest();
  }
  else {
  // code for IE6, IE5
    xmlhttp=new ActiveXObject("Microsoft.XMLHTTP");
  }

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var str = xmlhttp.responseText
      var v = str.split("##EOF##", 2)
      document.getElementById("specification").value = v[0];
      document.getElementById("signature").value = v[1];
      //document.getElementById("result_text").value = "Results";
    }
  }
 
  var e = document.getElementById("combobox")
  var str = e.options[e.selectedIndex].value
  var query = "?example="+str
  xmlhttp.open("GET", "load.py"+query, true)
  xmlhttp.send()

}

function clearAll() {
  document.getElementById("specification").value = "% SPECIFICATION";
  document.getElementById("signature").value = "% SIGNATURE";
  //document.getElementById("result_text").innerText = "";
  setText(document.getElementById("result_text"), "");
}
