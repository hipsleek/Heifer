import { FaGithub } from 'react-icons/fa';
import './NavigationBar.css';

function NavigationBar() {
  return (
    <header className="navbar">
      <div className="navbar-left">
        <span className="title">ESL Demo</span>
      </div>
      <div className="navbar-right">
        <span className="nav-item">
          Docs
        </span>
        <a
          href="https://github.com/songyahui/AlgebraicEffect/"
          target="_blank"
          rel="noopener noreferrer"
          className="nav-item"
        >
           <FaGithub style={{ background:"black"}} /> 
        </a>
      </div>
    </header>
  );
};

export default NavigationBar;