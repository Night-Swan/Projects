# Dots and Boxes

Dots and boxes is a game in witch 2 players place down lines one by one, competing to construct more boxes. 

# Files
We used SDK 19 (java version 19.0.2);
It requires Java Runtime version 63 or above meaning that Java 19 needs to be installed.

The src folder contains the source code of our project
The docs folder contains the JavaDoc documentation generated through InteliJ
The test folder contains our JUnit tests
The jar folder has all the executable files needed to start a server and clients in order to play the game
The game is composed of 3 main components, the game logic, the client and the server, with the addition of a package for the computer players. These can all be found in src.

# Usage
In order to run the server or client applications, you will need to open a command prompt and navigate to the jar directory (This can be done in a easier way by typing cmd in the search bar, while you are in the desired directory).

## Server

In order to start the server you will need to run the command:

> java -jar server.jar

You will then be asked for a port number, you can write in any unoccupied port you want, our port of choice was either 44444 or 4567.
After this you can put your feet up and wait for clients to connect to your server.

## Client
There are two types of client you could use, an AI client which will create a computer player that will endlessly play for you, and a normal client, which will allow you to play games of Dots and Boxes against any person on the server.

In order to start the AI client you will need to run the command:

> java -jar AIUI.jar

You will then be asked for a server address and a port number, if you are running the server input "LocalHost" as the server address otherwise, input the address of an existing server. For the port you will either have to enter the port the server owner chose. Afterwards you will need to mention the difficulty of the computer player, here you have 3 options easy, normal or hard. None of them are unfairly smart, but all of them can close boxes. Now your AI should be running and all that's left for you to do is watch and pray that the AI doesn't rebel against us.



In order to start the user client you will need to run the command:

> java -jar TUI.jar

You will then be asked for a server address and a port number, if you are running the server input "LocalHost" as the server address otherwise, input the address of an existing server. For the port you will either have to enter the port the server owner chose. Afterwards you will be asked for a username, This can be any name as long as it doesn't contain the character "~". Afterwards a list of commands will pop up, informing you of all the possible commands you can perform.
*in order to perform a move in the game you vile have to type "move x" where x represents the index of the line you want to draw.

Now that you're informed on how to run the client and server all that's left to do is enjoy a few games of Dots and Boxes. 