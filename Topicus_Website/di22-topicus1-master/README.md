
#  Topicus 1: Web Application

<!DOCTYPE  html>

<html>

<head>

<meta  charset="UTF-8">

</head>

<body>


<!DOCTYPE  html>

<html>

<head>

<meta  charset="UTF-8">

</head>

<body>

<h2>Description of Project:</h2>

<p><b>Company Description:</b> "Topicus.com is a leading provider of specialized software solutions for public and private sectors across Europe. We focus on vertical markets such as education, healthcare, government, and finance. Our goal is to simplify the lives of students, teachers, and board members by delivering mission-critical applications that meet their specific needs."</p>

<p>This project focuses on creating a centralized platform where parents and schools can easily register new students. The goal is to simplify and offer a shared environment for the enrollment process and improve communication between parents and schools. By providing such environment, we aim to streamline student registration, ensuring a smooth transition for new students while enabling parents to actively participate in their children's education.</p>

<p>This project is developed with <b>Maven</b> for dependency management, along with a <b>Java</b> back-end, with front-end using vanilla <b>JavaScript</b>, <b>HTML</b>, and <b>CSS</b>. The project uses the deployment server functionality of <b>Apache Tomcat 10.1</b>, and for all intents and purposes, testing was only done on a local machine/desktop server (the development team ran their servers on their local machines to develop the application). The external database used was provided by the University of Twente, and instructions regarding how to access the database will be provided in the installation section.</p>

  

<h2>Motivation Behind Project Development:</h2>

<p>The motivation behind the project was to produce an application that successfully displayed the functionalities required by the client (can be found in: <i>src/main/AssignmentsUpdatedFinalSubmission</i> as the file <i>Topicus 1_Product Features Overview</i>. However, the project was used as an opportunity to expand upon knowledge provided in the fourth module of BIT/TCS and display our skills in learning web programming and other concepts like security, database management, and of course understanding the Agile SCRUM Development Cycle.</p>

<h2>Table of Contents</h2>

<ul>

<li>Installation</li>

<li>Usage</li>

<li>Features</li>

<li>Authors</li>

<li>Acknowledgements</li>

<li>Frequently Asked Questions (FAQ)</li>

<li>Known Bugs In The System</li>

</ul>

<h2>Installation</h2>

<h3>To get started with the app, follow these steps: </h3>

1. Clone the repository to your local machine. You can use the following command:
   ```git
    git clone https://gitlab.utwente.nl/s2920344/di22-topicus1.git
    ```

2. Install Apache Tomcat on your machine. You can download Apache Tomcat from the official website: [https://tomcat.apache.org](https://tomcat.apache.org/). Choose the appropriate version for your operating system.

3. Set up Apache Tomcat with IntelliJ IDEA by following the instructions in this guide: [Tomcat Configuration in IntelliJ IDEA](https://www.jetbrains.com/help/idea/2021.1/creating-and-running-your-first-web-application.html#configure_tomcat).
4. Create an <b>`application.properties`</b> file. This is the configuration file which you need in order to connect to the database. It contains the database specification, as well as credentials. The file contents are <b>required</b> to be in the same format as shown below:
    ```properties
        db.name = DATABASE_NAME 
        db.schema  = DATABASE_SCHEMA
        db.username = DATABASE_USERNAME 
        db.password =  DATABASE_PASSWORD
   ```
   Ensure that you replace the credentials in the file with the correct database credentials for <b>your</b> setup. (or replace the file entirely if it has been provided to you). You need to add this file in two locations: 
   
    <b>a.</b> In the Apache Tomcat installation location, create a folder called <b>`topicus`</b>. Place the <b>`application.properties`</b> file inside this folder. (required for the application to work)
 
    <b>b.</b> In the same directory as the <b>`di22-topicus1`</b> project folder, create a folder called 	<b>`topicus`</b>. Place the same <b>`application.properties`</b> file inside this folder as well. (required for the unit tests to work)
 
    If you have done this correctly, you should have the following folder structure:
    ```
     Apache Tomcat Installation Location
         ├── bin
         ├── conf
         ├── lib
         ├── logs
         ├── temp
         └── topicus
             └── application.properties
		    
     Project Directory
         ├── di22-topicus1
         └── topicus
             └── application.properties 
     ```
   
     Please note that Tomcat does not need to be necessarily placed in the same parent directory as the Project Directory, the diagram is shown like this for convenience purposes. 
5. Run the application using an Apache Tomcat run configuration in IntelliJ IDEA. Make sure the run configuration is properly configured with the correct Tomcat version and deployment settings.
6. Access the application by opening a web browser and navigating to [http://localhost:8080/Topicus/](http://localhost:8080/Topicus/). Make sure to use the same port (8080) as specified in your Apache Tomcat run configuration.

That's it! You have successfully installed and set up the app on your local machine. You can now use and test the application by accessing the provided URL.

<h2>Usage</h2>

Consult the user manual that ca found under the name -> **"Topicus_1__User_Manual.pdf"**.

  

<h2>Features</h2>

The features can be found in the following document -> **"Topicus_1__Product_Features_Overview_1.pdf"**.

  

<h2>Authors</h2>

<p>Alexandru Lungu(s3006301) - a.lungu-1@student.utwente.nl</p>

<p>Narendra Setty (s2944200) - n.setty@student.utwente.nl</p>

<p>Martin Demirev (s2965046) - m.b.demirev@student.utwente.nl</p>

<p>Teodor Pintilie (s2920344) - t.pintilie@student.utwente.nl</p>

<p>Condu Alexandru-Stefan (s2769549) - a.condu@student.utwente.nl</p>

<p>Umair Aamir Mirza (s2928558) - u.a.mirza@student.utwente.nl</p>

  

<h2>Acknowledgments</h2>

<p>We would like to express our gratitude to Topicus for their inspiration and support during the development of this project. We appreciate the valuable insights and contributions from Topicus in creating a common environment for parents and schools.</p>

  

<h2>Frequently Asked Questions (FAQ)</h2>

<p>1. Can you register without an account? (Answer: Yes, you can, the method we use to keep track of your registration will be a guardian code that also serves as a log in method)</p>

<p>2. Can the registration created by a school admin be customizable, and if so to what extent? (Answer: Yes, a registration by a school admin can be customized. Customization includes: color changes for background, section header color and component input space color)</p>

<p>3. In case an administrator has to deal with a large amount of registrations, it there any way an admin can filter them? (Answer: Yes, the school admin dashboard uses filters to better facilitate the search procedures when coming down to data retrieval for a certain registration)</p>

<p>4. Is there a limit for the number of fields a certain form can have? (Answer: No, there is no such limit)</p>

<p>5. Am I able to create an account after I have decided to make a registration without an account? (Answer: Yes, it is possible, and the guardian code will be required in order to link your new profile to the existing registration)</p>

  

<h2>Known Bugs In The System</h2>

<p>1. Sometimes retrieving data from the backend needs a refresh so that it can provide the actual data stored into the database and not the HTML elements with their values.</p>

<p>2. The navigation bar sometimes bugs out when the resolution of the page reaches a certain dimension, but it does not affect the functionality.</p>

<p>3. The button on the profile page of the children sometimes require a longer duration of time in order to fully process the action. If the button still doesn't work, it's required that he page will be refreshed.</p>

<p>4. Some browsers (we have found the issue in Mozilla FireFox) have issues with the footer of the pages. Does not affect the functionality of the app and for Google Chrome or any other extensions that runs on Google Chrome the issue does not happen.</p>

<p>5. Sometimes the custom colors selected for a registration take a bit of time to load.</p>

<p>6. In the Apply For Registration Page, the sections can sometimes be duplicated. Due to time shortage, we weren't able to isolate the reason why this happens.</p>

<p>7. Apply For Registration can only work with TEXT, NUMBER and DATE(might give error). For this reason we recommend that the form builder only creates fields of the matching data types. This is to avoid any issues with the user interface and preventing any bugs. The front-end file implementation was made and the back-end implementation had a plan, but the time shortages did not allow the implementation.</p>

<p>8. Due to time limitations, show preview for creating a form as a school admin has some issues - not being able to display a small preview of the form with the selected colors.</p>

<p>9. Log out button for school admin role does not work.</p>

<p>10. Alerts shown on the Topicus Admin Dashboard, Topicus Add Admin, Topicus Add School pages are sometimes incorrect. For example when deleting an admin, the alert is shown, but the respective record is successfully deleted in the database. Due to the time constraints, we couldn't find the root cause of this bug.

<p>11. From a School Admin perspective, and you click on My Profile or Login, it reverts to the Guardian perspective.</p>

**NB**: Most of these issues emerged after we merged a branch and we had to solve 20+ merge conflicts.