const express = require('express')
const formidable = require('formidable')
const fs = require('fs')
const cmd = require('node-cmd')
const cors = require('cors')
const bodyParser = require('body-parser')
const app = express()
let processRef
app.use(cors())
app.use(bodyParser.text())

app.post('/files', (request, response) => {
  fs.writeFile(request.get('FileName'), request.body, (err) => {
    console.log(err)
    processRef = cmd.get('sml ' + request.get('FileName'))
    response.send("File created and process started.")
  })
})

app.post('/relational', (request, response) => {
  fs.writeFile(request.get('FileName'), request.body, (err) => {
    console.log(err)
    if (processRef === undefined) {
      response.status(400).send({
        error: "The ML file has not been defined. The file was not uploaded."
      })
    } else {
      let stream = processRef.stdout
      processRef.stdin.write("val T'' = " + request.body + "\n")
      stream.once('data', function (data) {
        response.send("Relational data file created and the process is using the data.")
      })
    }
  })
})

app.post('/document', (request, response) => {
  fs.writeFile(request.get('FileName'), request.body, (err) => {
    console.log(err)
    if (processRef === undefined) {
      response.status(400).send({
        error: "The ML file has not been defined. The file was not uploaded."
      })
    } else {
      let stream = processRef.stdout
      processRef.stdin.write("val E'' = " + request.body + "\n")
      stream.once('data', function (data) {
        response.send("Document data file created and the process is using the data.")
      })
    }
  })
})

app.post('/graph', (request, response) => {
  fs.writeFile(request.get('FileName'), request.body, (err) => {
    console.log(err)
    if (processRef === undefined) {
      response.status(400).send({
        error: "The ML file has not been defined. The file was not uploaded."
      })
    } else {
      let stream = processRef.stdout
      processRef.stdin.write("val G'' = " + request.body + "\n")
      stream.once('data', function (data) {
        response.send("Graph data file created and the process is using the data.")
      })
    }
  })
})

app.post('/ml', (request, response) => {
  if (processRef === undefined) {
    response.status(400).send({
      error: "The ML file has not been defined."
    })
  } else {
    let stream = processRef.stdout
    processRef.stdin.write(request.body + "\n")
    stream.once('data', function (data) {
      response.send(data)
    })
  }
})

const PORT = 3001
app.listen(PORT, () => {
  console.log(`Server running on port ${PORT}`)
})